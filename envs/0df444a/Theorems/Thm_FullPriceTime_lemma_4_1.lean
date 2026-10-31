-- Prove2me | Theorems.Thm_FullPriceTime_lemma_4_1
-- name    : FullPriceTime.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:48:55.043734+00:00
-- url     : https://prove2.me/theorems/1457b09e-a3a2-4fe8-a27e-70ae8c82d544
-- title:
--   Lemma 4.1: a gig worker who buys has $\chi=\theta$ and $O'(c_O)=-1/\theta$ at the optimum (corrected: interior optimum)
-- statement:
--   Let $U$ and $O$ satisfy the standing assumptions, let the consumer be paid the linear wage $\Pi_\theta(t_w)=\theta t_w$ with $\theta>0$, and let the discrete service have price $r\ge 0$ and time commitment $\delta\ge 0$. Let $(t^B_l,c^B_l,t^B_w,c^B_O)$ be an optimal plan of the buyer's problem (PC) with $y=1$, at which $U$ is differentiable with $\partial U/\partial c_l\neq 0$. Then
--
--   1. both constraints bind: $t^B_l=T-t^B_w-O(c^B_O)-\delta$ and $c^B_l=\theta t^B_w-c^B_O-r$;
--   2. if moreover $t^B_l>0$ and $c^B_l>0$, the marginal rate of substitution equals the wage:
--   $$\chi\big(T-t^B_w-O(c^B_O)-\delta,\ \theta t^B_w-c^B_O-r\big)=\theta;$$
--   3. if $c^B_O>0$ and $O$ is differentiable at $c^B_O$, then $O'(c^B_O)=-1/\theta$.
--
--   These are the first-order conditions of a buying gig worker: at the margin, an hour of leisure is worth exactly the wage, and a dollar spent on overhead reduction buys back $1/\theta$ hours.
--
--   **Formalization Note** "Found from" is read as necessary conditions satisfied by every optimal plan. The derivative $O'(c_O)$ is any $d$ with `HasDerivAt O d c_O`.
--
--   Differences from the source:
--   - correction: χ = θ and O′(c^B_O) = −1/θ at every optimum → χ = θ only when t_l > 0 and c_l > 0 at the optimum, and the O′ equation only when c_O > 0 (the binding identities and the O′ equation need no interiority of t_l, c_l); reason: false at corner optima (T = 3, θ = 1, O(c) = e^{−c}, r = δ = 0: U = c_l has the optimum (0,2,2,0) with χ = 0; U = t_l + c_l/2 has the optimum (2,0,0,0) with χ = 2; with θ = 1/2 and U = √t_l + √c_l the optimum has c_O = 0 and O′(0) = −1 ≠ −2)
--   - encoding: partial derivatives of U and O′ used without stating their existence → U differentiable at (t_l, c_l) with ∂U/∂c_l ≠ 0, and O′(c_O) as any d with HasDerivAt O d c_O; reason: χ and O′ are undefined elsewhere, so only those points are excluded
--   - encoding: U defined on the quadrant t_l, c_l ≥ 0 → U : ℝ × ℝ → ℝ with every standing assumption imposed on the closed quadrant, and differentiability at the optimum as Fréchet differentiability of this function; reason: (PC) evaluates U only on the quadrant; at an interior point the values outside it do not matter
--   - reading: the optimal actions "are found from" the equations → every optimal plan satisfies them (necessary conditions); reason: the proof on p.32 shows exactly that the optimum satisfies the first-order conditions
--   - reading: optimal actions (t^B_w, c^B_O) with t^B_l, c^B_l found from the binding constraints → any maximizer of (PC) with y = 1 fixed, with the binding identities as part of the conclusion; reason: p.32 obtains t^B_l, c^B_l from the binding constraints; under the hypotheses every maximizer binds, so the paper's point is (t_l, c_l)
--   - reading: r, δ unrestricted → r, δ ≥ 0; reason: r is a price paid from earnings (r ∈ ℝ₊, p.14) and δ a block of time
--   - reading: U concave in both arguments → concave in each argument separately on the quadrant; reason: the weaker of the two readings (joint concavity implies it); the result does not use concavity
--   - encoding: O decreasing → strictly decreasing on c_O ≥ 0; reason: a non-increasing strictly convex function on [0,∞) is strictly decreasing, so no instance changes
--   - encoding: θ the wage → θ > 0; reason: a wage per time unit is positive (the paper's η = θ > 0)
--   - encoding: objective U(t_l, c_l) + Vy → U(t_l, c_l); reason: y is fixed, so Vy is a constant
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, Lemma 4 part 1, p.32

import Mathlib
import Definitions.Def_FullPriceTime_StandingAssumptions
import Definitions.Def_FullPriceTime_linearCompensation
import Definitions.Def_FullPriceTime_IsOptimalPlan
import Definitions.Def_FullPriceTime_mrs

namespace FullPriceTime

/-- **Lemma 4, part 1 (buyer's first-order conditions), corrected: interior optimum.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, Appendix A.2, Lemma 4 part 1, p.32 (PDF p.32): "Under the linear
compensation structure defined in (1), 1. The optimal actions for a consumer who does purchase the
discrete service are found from χ(T − t^B_w − O(c^B_O) − δ, θt^B_w − c^B_O − r) = θ, and
O′(c^B_O) = −1/θ".

Let `U, O` satisfy the standing assumptions, let the wage be `θ > 0` with compensation
`Π_θ(t_w) = θ t_w`, and let `r, δ ≥ 0`. Let `p` be an optimal plan of the buyer's problem
(`y = 1`) at which `U` is differentiable with `∂U/∂c_l ≠ 0`. Then both constraints bind,
`t_l = T − t_w − O(c_O) − δ` and `c_l = θ t_w − c_O − r` (the paper's expressions for
`t^B_l, c^B_l`, p.32); if moreover `t_l > 0` and `c_l > 0`, then `χ` at that point equals `θ`;
and if `c_O > 0` and `O` has derivative `d` at `c_O`, then `d = −1/θ`.

**Formalization Note** "Found from" is read as necessary conditions satisfied by every optimal
plan (the proof, p.32, shows exactly this). The hypotheses `t_l > 0`, `c_l > 0` (for `χ` only) and
`c_O > 0` (for `O′` only) correct the printed lemma, which is false at corner optima. Differentiability
of `U` and `∂U/∂c_l ≠ 0` at the optimum, and of `O` at `c_O`, are where `χ` and `O′` are
defined. -/
theorem lemma_4_1 (T θ r δ : ℝ) (U : ℝ × ℝ → ℝ) (O : ℝ → ℝ)
    (hUO : StandingAssumptions U O) (hθ : 0 < θ) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (p : Plan)
    (hp : IsOptimalPlan T U O (linearCompensation θ) r δ 1 p)
    (hdiff : DifferentiableAt ℝ U (p.tl, p.cl))
    (hUc : fderiv ℝ U (p.tl, p.cl) (0, 1) ≠ 0) :
    p.tl = T - p.tw - O p.cO - δ ∧
    p.cl = θ * p.tw - p.cO - r ∧
    (0 < p.tl → 0 < p.cl → mrs U (T - p.tw - O p.cO - δ, θ * p.tw - p.cO - r) = θ) ∧
    (0 < p.cO → ∀ d : ℝ, HasDerivAt O d p.cO → d = -1 / θ) := by sorry

end FullPriceTime
