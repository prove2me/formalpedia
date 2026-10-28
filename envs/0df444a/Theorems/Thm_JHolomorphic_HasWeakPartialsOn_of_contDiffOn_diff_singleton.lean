-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn_diff_singleton
-- name    : JHolomorphic.HasWeakPartialsOn.of_contDiffOn_diff_singleton
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T21:14:38.354986+00:00
-- url     : https://prove2.me/theorems/9f78303b-2cc9-47b9-96c5-cfaa91ce776a
-- title:
--   A point is removable for weak partial derivatives
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $U\subseteq\mathbb{C}$ open, $z_0\in U$, and $u:U\to E$ continuous on $U$ and of class $C^1$ on $U\setminus\{z_0\}$, with
--   $$\int_U\|Du(z)\|^p\,dz<\infty\qquad\text{for some }p\ge 1 .$$
--   Then the classical partial derivatives $\partial_s u=Du(\cdot)\,1$ and $\partial_t u=Du(\cdot)\,i$ (defined off $z_0$) are weak partial derivatives of $u$ on all of $U$, and both lie in $L^p(U)$.
--
--   A single point is removable for weak differentiability of a continuous function whose classical derivative is $p$-integrable. This lets a map that is smooth off one point be treated as a Sobolev map across it.
--
--   **Formalization Note** Weak partial derivatives are `JHolomorphic.HasWeakPartialsOn U u (fun z => fderiv ℝ u z 1) (fun z => fderiv ℝ u z Complex.I)`, tested against real `C^∞` functions with compact support in `U`. The integrability hypothesis is a lower integral of `ENNReal.ofReal (‖fderiv ℝ u z‖ ^ p)`; the `L^p` conclusions are `MemLp … (ENNReal.ofReal p) (volume.restrict U)`.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, proof of Proposition 4.8

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal

/-- Weak partial derivatives across a point. Let `U ⊆ ℂ` be open, `z₀ ∈ U`, and `u` continuous on
`U` and `C¹` on `U \ {z₀}`, with `∫_U ‖Du‖^p < ∞` for some `p ≥ 1`. Then the classical partial
derivatives `Du(z) 1` and `Du(z) i` are weak partial derivatives of `u` on all of `U`, and both lie
in `L^p(U)`. -/
theorem HasWeakPartialsOn.of_contDiffOn_diff_singleton {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) {u : ℂ → E} (hc : ContinuousOn u U) (hu : ContDiffOn ℝ 1 u (U \ {z₀}))
    {p : ℝ} (hp : 1 ≤ p) (hint : ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ p) < ⊤) :
    HasWeakPartialsOn U u (fun z => fderiv ℝ u z 1) (fun z => fderiv ℝ u z Complex.I) ∧
      MemLp (fun z => fderiv ℝ u z 1) (ENNReal.ofReal p) (volume.restrict U) ∧
      MemLp (fun z => fderiv ℝ u z Complex.I) (ENNReal.ofReal p) (volume.restrict U) := by
  sorry

end JHolomorphic
