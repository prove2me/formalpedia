-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_isClosedImmersion_iff_pullRatio
-- name    : GlobalTheory.ProjSpace.isClosedImmersion_iff_pullRatio
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:09:05.596025+00:00
-- url     : https://prove2.me/theorems/8a0c7863-e024-5cff-b24a-d37fd6581d9f
-- title:
--   Proj Space: is Closed Immersion iff pull Ratio
-- statement:
--   The Proj Space construction uses the is Closed Immersion iff pull Ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L320-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L320-L338

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable {R : Type} [CommRing R] {N : ℕ} {Y Z : Scheme.{0}}

theorem GlobalTheory.ProjSpace.isClosedImmersion_iff_pullRatio (φ : Y ⟶ PSpace R N) {U : Fin (N + 1) → Y.Opens}
    (hU : ∀ i, φ ⁻¹ᵁ chart R N i = U i) :
    IsClosedImmersion φ ↔ ∀ i, IsAffineOpen (U i) ∧ Function.Surjective
      (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) (U i)).hom (pullRatio φ (U i) i (hU i).ge)) := by sorry
