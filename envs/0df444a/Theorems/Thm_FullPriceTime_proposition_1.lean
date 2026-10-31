-- Prove2me | Theorems.Thm_FullPriceTime_proposition_1
-- name    : FullPriceTime.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:58.277991+00:00
-- url     : https://prove2.me/theorems/c395d8fa-5071-4316-98d4-df6352f80fc3
-- title:
--   Proposition 1: gig workers are full-price decision-makers with $\eta=\theta$, and $\chi=\theta$ (corrected: interior optimum)
-- statement:
--   Let $U$ and $O$ satisfy the standing assumptions, and let the consumer be a gig worker, paid the linear wage $\Pi_\theta(t_w)=\theta t_w$ with $\theta>0$. Then:
--
--   1. the consumer is a **full-price decision-maker** (Definition 1);
--   2. the conversion rate of time into money is her wage, $\eta=\theta$: for all $r,\delta,\hat r,\hat\delta\ge 0$ with $(\hat r,\hat\delta)$ feasible,
--   $$r+\theta\delta=\hat r+\theta\hat\delta\ \Longrightarrow\ u^B(\theta,r,\delta)=u^B(\theta,\hat r,\hat\delta);$$
--   3. her marginal rate of substitution of time for money is her wage, whether she buys ($j=B$, any $r,\delta\ge 0$) or not ($j=NB$): at every optimal plan $(t^j_l,c^j_l,t^j_w,c^j_O)$ of (PC) with $t^j_l>0$ and $c^j_l>0$ at which $U$ is differentiable with $\partial U/\partial c_l\neq 0$,
--   $$\chi(t^j_l,c^j_l)=\theta .$$
--
--   In words: gig workers have iso-utility curves in the $(r,\delta)$ plane that are parallel lines of slope $\theta$, so the classical full-price model $r+\theta\delta$ of the queueing-pricing literature is exact for them, with the waiting cost per unit of time equal to the wage.
--
--   **Formalization Note** $u^B$ is a supremum in the extended reals. Clause 2 implies clause 1; both are stated, clause 1 being the paper's sentence and clause 2 its constant ("furthermore, $\eta=\theta$", p.32).
--
--   Differences from the source:
--   - correction: χ(t^j_l, c^j_l) = θ at every optimum → only when t_l > 0 and c_l > 0 at the optimum; reason: false at corner optima (T = 3, θ = 1, O(c) = e^{−c}: for U = c_l the non-buyer optimum (0,2,2,0) has χ = 0; for U = t_l + c_l/2 the optimum (2,0,0,0) has χ = 2)
--   - encoding: partial derivatives of U used without stating their existence → U differentiable at (t_l, c_l) with ∂U/∂c_l ≠ 0; reason: χ is undefined elsewhere, so only those points are excluded
--   - encoding: U defined on the quadrant t_l, c_l ≥ 0 → U : ℝ × ℝ → ℝ with every standing assumption imposed on the closed quadrant, and differentiability at the optimum as Fréchet differentiability of this function; reason: (PC) evaluates U only on the quadrant; at an interior point the values outside it do not matter
--   - encoding: u^B the "optimal utility" → supremum in EReal over the buyer's feasible plans; reason: equals the optimum when attained, and gives −∞/+∞ instead of a junk value when infeasible/unbounded
--   - reading: (r̂, δ̂) feasible means (PC) has a non-empty feasible set → feasible with y = 1; reason: u^B is the buyer's utility, and with y = 0 (r̂, δ̂) does not enter (PC)
--   - reading: prices and time commitments unrestricted → r, δ, r̂, δ̂ ≥ 0 in Definition 1 and in clauses 2 and 3; reason: r is a price paid from earnings (r ∈ ℝ₊, p.14), δ a block of time; with r̂ = −5/2, δ̂ = 5/2 (T = 3, θ = 1, U = c_l, O = e^{−c}) the full-price property fails
--   - reading: (r, δ) free in Definition 1 → universally quantified, not required feasible; reason: the page requires feasibility only of (r̂, δ̂)
--   - reading: the optimal (t^j_l, c^j_l), j ∈ {NB, B} → any maximizer of (PC) with y ∈ {0, 1} fixed; reason: the paper's optimal actions are these maximizers (p.8, p.32)
--   - reading: U concave in both arguments → concave in each argument separately on the quadrant; reason: the weaker of the two readings (joint concavity implies it); the result does not use concavity
--   - encoding: O decreasing → strictly decreasing on c_O ≥ 0; reason: a non-increasing strictly convex function on [0,∞) is strictly decreasing, so no instance changes
--   - encoding: θ the wage → θ > 0; reason: a wage per time unit is positive (the paper's η = θ > 0)
--   - encoding: objective U(t_l, c_l) + Vy → U(t_l, c_l); reason: y is fixed, so Vy is a constant
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, Proposition 1, p.8; proof Appendix A.2, p.32

import Mathlib
import Definitions.Def_FullPriceTime_StandingAssumptions
import Definitions.Def_FullPriceTime_linearCompensation
import Definitions.Def_FullPriceTime_IsFeasiblePair
import Definitions.Def_FullPriceTime_buyerUtility
import Definitions.Def_FullPriceTime_IsFullPriceDecisionMaker
import Definitions.Def_FullPriceTime_IsOptimalPlan
import Definitions.Def_FullPriceTime_mrs

namespace FullPriceTime

/-- **Proposition 1: gig workers are full-price decision-makers with `η = θ`, and their marginal
rate of substitution of time for money equals their wage (corrected: interior optimum).**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §3.1, Proposition 1, p.8 (PDF p.8): "Consumers, who are gig workers
with compensation structure definition (1), are full-price decision-makers. Furthermore, gig
workers' marginal rate of substitution of time for money is their wages, i.e., χ(t^j_l, c^j_l) = θ,
for j ∈ {NB, B}. That is, gig workers have iso-utility curves with constant slopes, and that slope
is equal to their wages." Proof, Appendix A.2, p.32: "… are full-price decision-makers and
furthermore, η = θ."

Let `U, O` satisfy the standing assumptions, and let the consumer be paid the wage `θ > 0`,
`Π_θ(t_w) = θ t_w`. Then
1. the consumer is a full-price decision-maker (Definition 1);
2. the constant of Definition 1 can be taken to be `η = θ`: for all `r, δ, r̂, δ̂ ≥ 0` with
   `(r̂, δ̂)` feasible and `r + θδ = r̂ + θδ̂`, `u^B(θ, r, δ) = u^B(θ, r̂, δ̂)`;
3. for `y ∈ {0, 1}` (non-buyer and buyer) and all `r, δ ≥ 0`, at every optimal plan of (PC) with
   purchase decision `y` that has `t_l > 0`, `c_l > 0` and at which `U` is differentiable with
   `∂U/∂c_l ≠ 0`, `χ(t_l, c_l) = θ`.

**Formalization Note** `u^B` is the supremum in `EReal` (`buyerUtility`). The interiority
hypotheses `t_l > 0`, `c_l > 0` in clause 3 correct the printed proposition, which is false at
corner optima; differentiability and `∂U/∂c_l ≠ 0` are where `χ` is defined. -/
theorem proposition_1 (T θ : ℝ) (U : ℝ × ℝ → ℝ) (O : ℝ → ℝ)
    (hUO : StandingAssumptions U O) (hθ : 0 < θ) :
    IsFullPriceDecisionMaker T U O (linearCompensation θ) ∧
    (∀ r δ r' δ' : ℝ, 0 ≤ r → 0 ≤ δ → 0 ≤ r' → 0 ≤ δ' →
      IsFeasiblePair T O (linearCompensation θ) r' δ' →
      r + θ * δ = r' + θ * δ' →
      buyerUtility T U O (linearCompensation θ) r δ =
        buyerUtility T U O (linearCompensation θ) r' δ') ∧
    (∀ y ∈ ({0, 1} : Set ℝ), ∀ r δ : ℝ, 0 ≤ r → 0 ≤ δ → ∀ p : Plan,
      IsOptimalPlan T U O (linearCompensation θ) r δ y p →
      0 < p.tl → 0 < p.cl →
      DifferentiableAt ℝ U (p.tl, p.cl) →
      fderiv ℝ U (p.tl, p.cl) (0, 1) ≠ 0 →
      mrs U (p.tl, p.cl) = θ) := by sorry

end FullPriceTime
