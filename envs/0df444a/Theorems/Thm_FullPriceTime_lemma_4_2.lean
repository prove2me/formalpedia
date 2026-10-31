-- Prove2me | Theorems.Thm_FullPriceTime_lemma_4_2
-- name    : FullPriceTime.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:44.976335+00:00
-- url     : https://prove2.me/theorems/bfea5f7d-3e55-43fb-9b26-b4c73a68a0c2
-- title:
--   Lemma 4.2: a gig worker who does not buy has $\chi=\theta$ and $O'(c_O)=-1/\theta$ at the optimum (corrected: interior optimum)
-- statement:
--   Let $U$ and $O$ satisfy the standing assumptions and let the consumer be paid the linear wage $\Pi_\theta(t_w)=\theta t_w$ with $\theta>0$. Let $(t^{NB}_l,c^{NB}_l,t^{NB}_w,c^{NB}_O)$ be an optimal plan of the non-buyer's problem (PC) with $y=0$, at which $U$ is differentiable with $\partial U/\partial c_l\neq 0$. Then
--
--   1. both constraints bind: $t^{NB}_l=T-t^{NB}_w-O(c^{NB}_O)$ and $c^{NB}_l=\theta t^{NB}_w-c^{NB}_O$;
--   2. if moreover $t^{NB}_l>0$ and $c^{NB}_l>0$, the marginal rate of substitution equals the wage:
--   $$\chi\big(T-t^{NB}_w-O(c^{NB}_O),\ \theta t^{NB}_w-c^{NB}_O\big)=\theta;$$
--   3. if $c^{NB}_O>0$ and $O$ is differentiable at $c^{NB}_O$, then $O'(c^{NB}_O)=-1/\theta$.
--
--   Together with part 1 this shows that the gig worker's valuation of time is her wage whether or not she buys the discrete service.
--
--   **Formalization Note** "Found from" is read as necessary conditions satisfied by every optimal plan. The derivative $O'(c_O)$ is any $d$ with `HasDerivAt O d c_O`. The price and time commitment of the service are carried as arbitrary reals; with $y=0$ they are multiplied by $0$.
--
--   Differences from the source:
--   - correction: χ = θ and O′(c^{NB}_O) = −1/θ at every optimum → χ = θ only when t_l > 0 and c_l > 0 at the optimum, and the O′ equation only when c_O > 0 (the binding identities and the O′ equation need no interiority of t_l, c_l); reason: false at corner optima (T = 3, θ = 1, O(c) = e^{−c}: U = c_l has the optimum (0,2,2,0) with χ = 0; U = t_l + c_l/2 has the optimum (2,0,0,0) with χ = 2; with θ = 1/2 and U = √t_l + √c_l the optimum has c_O = 0 and O′(0) = −1 ≠ −2)
--   - encoding: partial derivatives of U and O′ used without stating their existence → U differentiable at (t_l, c_l) with ∂U/∂c_l ≠ 0, and O′(c_O) as any d with HasDerivAt O d c_O; reason: χ and O′ are undefined elsewhere, so only those points are excluded
--   - encoding: U defined on the quadrant t_l, c_l ≥ 0 → U : ℝ × ℝ → ℝ with every standing assumption imposed on the closed quadrant, and differentiability at the optimum as Fréchet differentiability of this function; reason: (PC) evaluates U only on the quadrant; at an interior point the values outside it do not matter
--   - reading: the optimal actions "are found from" the equations → every optimal plan satisfies them (necessary conditions); reason: the proof on p.32 shows exactly that the optimum satisfies the first-order conditions
--   - reading: optimal actions (t^{NB}_w, c^{NB}_O) with t^{NB}_l, c^{NB}_l found from the binding constraints → any maximizer of (PC) with y = 0 fixed, with the binding identities as part of the conclusion; reason: p.32 obtains t^{NB}_l, c^{NB}_l from the binding constraints; under the hypotheses every maximizer binds
--   - encoding: the non-buyer's problem has no r, δ → arbitrary r, δ multiplied by y = 0; reason: the constraints are identical for every r, δ
--   - reading: U concave in both arguments → concave in each argument separately on the quadrant; reason: the weaker of the two readings (joint concavity implies it); the result does not use concavity
--   - encoding: O decreasing → strictly decreasing on c_O ≥ 0; reason: a non-increasing strictly convex function on [0,∞) is strictly decreasing, so no instance changes
--   - encoding: θ the wage → θ > 0; reason: a wage per time unit is positive (the paper's η = θ > 0)
--   - encoding: objective U(t_l, c_l) + Vy → U(t_l, c_l); reason: y is fixed, so Vy is a constant
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, Lemma 4 part 2, p.32

import Mathlib
import Definitions.Def_FullPriceTime_StandingAssumptions
import Definitions.Def_FullPriceTime_linearCompensation
import Definitions.Def_FullPriceTime_IsOptimalPlan
import Definitions.Def_FullPriceTime_mrs

namespace FullPriceTime

/-- **Lemma 4, part 2 (non-buyer's first-order conditions), corrected: interior optimum.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, Appendix A.2, Lemma 4 part 2, p.32 (PDF p.32): "Under the linear
compensation structure defined in (1), … 2. The optimal actions for a consumer who does not
purchase the discrete service are found from χ(T − t^NB_w − O(c^NB_O), θt^NB_w − c^NB_O) = θ, and
O′(c^NB_O) = −1/θ."

Let `U, O` satisfy the standing assumptions and let the wage be `θ > 0` with compensation
`Π_θ(t_w) = θ t_w`. Let `p` be an optimal plan of the non-buyer's problem (`y = 0`, so price and
time commitment do not enter) at which `U` is differentiable with `∂U/∂c_l ≠ 0`. Then both
constraints bind, `t_l = T − t_w − O(c_O)` and `c_l = θ t_w − c_O`; if moreover `t_l > 0` and
`c_l > 0`, then `χ` at that point equals `θ`; and if `c_O > 0` and `O` has derivative `d` at `c_O`,
then `d = −1/θ`.

**Formalization Note** With `y = 0` the price `r` and the time commitment `δ` are multiplied by
`0` in (PC); they are arbitrary reals here. "Found from" is read as necessary conditions. The
hypotheses `t_l > 0`, `c_l > 0` (for `χ` only) and `c_O > 0` (for `O′` only) correct the printed
lemma, which is false at corner optima. Differentiability of `U` and `∂U/∂c_l ≠ 0` at the optimum, and of `O` at `c_O`, are where
`χ` and `O′` are defined. -/
theorem lemma_4_2 (T θ r δ : ℝ) (U : ℝ × ℝ → ℝ) (O : ℝ → ℝ)
    (hUO : StandingAssumptions U O) (hθ : 0 < θ) (p : Plan)
    (hp : IsOptimalPlan T U O (linearCompensation θ) r δ 0 p)
    (hdiff : DifferentiableAt ℝ U (p.tl, p.cl))
    (hUc : fderiv ℝ U (p.tl, p.cl) (0, 1) ≠ 0) :
    p.tl = T - p.tw - O p.cO ∧
    p.cl = θ * p.tw - p.cO ∧
    (0 < p.tl → 0 < p.cl → mrs U (T - p.tw - O p.cO, θ * p.tw - p.cO) = θ) ∧
    (0 < p.cO → ∀ d : ℝ, HasDerivAt O d p.cO → d = -1 / θ) := by sorry

end FullPriceTime
