-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_PhaseGeometry_anchored_polynomial_grid_phases
-- name    : OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:05:43.932091+00:00
-- url     : https://prove2.me/theorems/0cccfbcd-fac8-4328-8ad1-e8838e32f184
-- title:
--   OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/AnchoredGridPhases.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/AnchoredGridPhases.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.PhaseGeometry`, with `open Set Complex Bundle Manifold`, `open scoped ContDiff Matrix Topology Manifold BigOperators`, `open SmallModes RealModes WeightedEstimates Set`):
--
--   ```lean
--   theorem anchored_polynomial_grid_phases {T : Set PhaseMean.Tensor}
--       (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
--       (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
--       (R c A b K : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) (hK : 0 ≤ K) :
--       ∃ stock : Finset PhaseBasis, ∃ ε C δ z₀ W κ : ℝ,
--         0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < W ∧ 0 < κ ∧
--         ∀ z : ℝ, 0 < z → z ≤ z₀ →
--         ∀ F : RField 4, ContDiff ℝ ∞ F → WeightedBound univ z 3 A F →
--         ∀ H : Base → PhaseMean.Tensor,
--           (∀ x y, ‖H y-H x‖ ≤ K*‖y-x‖) →
--         ∀ s : Finset PhaseGrid.Index,
--           (∀ a ∈ s, ∃ x : Base, ‖x-z^6 • PhaseGrid.center a‖ ≤ 3*z^6 ∧
--             ‖firstJetPair F x‖ ≤ R ∧
--             c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 ∧
--             b ≤ ‖realSecondTensor F x‖ ∧ H x ∈ T) →
--         ∃ (P : {a // a ∈ s} → PhaseBasis) (w : {a // a ∈ s} × Fin 3 → ℝ),
--           (∀ a, P a ∈ stock) ∧
--           (∀ a i, ‖(P a).ξ i‖ ≤ C ∧ ‖(P a).Q i‖ ≤ C) ∧
--           (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
--           (∀ a y G H', y ∈ tsupport (PhaseGrid.cutoff (z^6) a.val) →
--             ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
--             ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
--             c/4 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
--             b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ (P a).Q i H' ∧
--               (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-((P a).ξ i).2,((P a).ξ i).1)‖ ∧
--               Good (realSecondTensor G y) ((P a).ξ i)) ∧
--           (∀ a d y G, a ≠ d → y ∈ tsupport (PhaseGrid.cutoff (z^6) a.1.val) →
--             y ∈ tsupport (PhaseGrid.cutoff (z^6) d.1.val) →
--             ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
--             ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 →
--             κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
--               (-(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).1)‖ ∧
--             κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
--               (-(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).1)‖ ∧
--             Good (realSecondTensor G y) (w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2) ∧
--             Good (realSecondTensor G y) (w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.PhaseGrid.Index`, `OAI.ClosedSurfaceR4.PhaseGrid.center` and `OAI.ClosedSurfaceR4.PhaseGrid.cutoff` (definitions bundle `OAIQ249SI000` of this split); `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor` and `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.PhaseGrid.Base`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor` and `OAI.ClosedSurfaceR4.SmallModes.Base` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.RealModes.TangentPair` and `OAI.ClosedSurfaceR4.RealModes.firstJetPair` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.RealModes.secondJetTriple` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` (definitions bundle `OAIQ249SI013` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/AnchoredGridPhases.lean (declaration OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases)

import Mathlib
import Definitions.Def_OAIQ249SI000
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates Set

theorem anchored_polynomial_grid_phases {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
    (R c A b K : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ stock : Finset PhaseBasis, ∃ ε C δ z₀ W κ : ℝ,
      0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < W ∧ 0 < κ ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ →
      ∀ F : RField 4, ContDiff ℝ ∞ F → WeightedBound univ z 3 A F →
      ∀ H : Base → PhaseMean.Tensor,
        (∀ x y, ‖H y-H x‖ ≤ K*‖y-x‖) →
      ∀ s : Finset PhaseGrid.Index,
        (∀ a ∈ s, ∃ x : Base, ‖x-z^6 • PhaseGrid.center a‖ ≤ 3*z^6 ∧
          ‖firstJetPair F x‖ ≤ R ∧
          c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 ∧
          b ≤ ‖realSecondTensor F x‖ ∧ H x ∈ T) →
      ∃ (P : {a // a ∈ s} → PhaseBasis) (w : {a // a ∈ s} × Fin 3 → ℝ),
        (∀ a, P a ∈ stock) ∧
        (∀ a i, ‖(P a).ξ i‖ ≤ C ∧ ‖(P a).Q i‖ ≤ C) ∧
        (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        (∀ a y G H', y ∈ tsupport (PhaseGrid.cutoff (z^6) a.val) →
          ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
          ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
          c/4 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
          b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ (P a).Q i H' ∧
            (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-((P a).ξ i).2,((P a).ξ i).1)‖ ∧
            Good (realSecondTensor G y) ((P a).ξ i)) ∧
        (∀ a d y G, a ≠ d → y ∈ tsupport (PhaseGrid.cutoff (z^6) a.1.val) →
          y ∈ tsupport (PhaseGrid.cutoff (z^6) d.1.val) →
          ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
          ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 →
          κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
            (-(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).1)‖ ∧
          κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
            (-(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).1)‖ ∧
          Good (realSecondTensor G y) (w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2) ∧
          Good (realSecondTensor G y) (w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2)) := by
  sorry

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end
