-- Prove2me | Theorems.Thm_GPhNGIDiffusion_OccupationCLT_proposition_3_7
-- name    : GPhNGIDiffusion.OccupationCLT.proposition_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:38.235128+00:00
-- url     : https://prove2.me/theorems/ce254a3a-88e1-4997-8d6c-70e087f4c0e1
-- title:
--   Proposition 3.7, p. 16 — E L^{ϵ,x}_t ≤ Cϵe^{ct}(1 + |x|)(1 + t) for the weighted occupation time of e′X near 0
-- statement:
--   For $\epsilon>0$ let $L^{\epsilon,x}_t=\int_0^t\big[-\epsilon^{-2}(e'X^x_s)^2+1\big]\mathbf 1_{\{|e'X^x_s|\le\epsilon\}}\,ds$ be the weighted occupation time of the limiting diffusion near the hyperplane $e'x=0$. There are constants $C,c>0$, independent of $\epsilon$, $t$ and $x$, such that for all $\epsilon>0$, $t\ge0$ and $x\in\mathbb R^d$,
--   $$
--   \mathbb EL^{\epsilon,x}_t\le C\epsilon e^{ct}(1+|x|)(1+t).
--   $$
--
--   Letting $\epsilon\to0$ shows that $e'X^x$ spends zero Lebesgue time on the hyperplane where the drift is not differentiable, which is what Lemma 3.5 needs.
--
--   **Formalization Note** The display carries the dependence on $x$ explicitly as $(1+|x|)$, so the constants are taken independent of $x$ as well.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 16, Proposition 3.7 (proof pp. 34–35)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Occupation
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

/-- Proposition 3.7, p. 16. There are constants `C, c > 0`, independent of `ϵ`, `t` (and `x`),
with `E L^{ϵ,x}_t ≤ Cϵ e^{ct}(1 + |x|)(1 + t)` for the weighted occupation time
`L^{ϵ,x}_t = ∫₀ᵗ (1 − (e′X^x_s)²/ϵ²) 1{|e′X^x_s| ≤ ϵ} ds`. -/
theorem proposition_3_7 {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ϵ : ℝ, 0 < ϵ → ∀ (t : ℝ≥0) (x : E d),
      ∫ ω, weightedOcc X ϵ x t ω ∂P ≤ C * ϵ * Real.exp (c * t) * (1 + ‖x‖) * (1 + t) := by sorry

end GPhNGIDiffusion.OccupationCLT
