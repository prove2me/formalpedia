-- Prove2me | Theorems.Thm_GlobalTheory_GlobalFunctions_eq_zero_of_fibres
-- name    : GlobalTheory.GlobalFunctions.eq_zero_of_fibres
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:55:36.844661+00:00
-- url     : https://prove2.me/theorems/cb6ddb21-5d5c-4bde-ac56-1c8bb2461edf
-- title:
--   Global Functions: eq zero of fibres
-- statement:
--   The Global Functions construction uses the eq zero of fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L55-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L55-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions

theorem GlobalTheory.GlobalFunctions.eq_zero_of_fibres (hI : FibreInjective) (hD : SmoothDescent) {R B C : Type} [CommRing R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C]
    (f g : B →ₐ[R] C) (r : B →ₐ[R] R)
    (hk : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] B),
      f.toLinearMap.baseChange k x = g.toLinearMap.baseChange k x →
      r.toLinearMap.baseChange k x = 0 → x = 0)
    (b : B) (hb : f b = g b) (hr : r b = 0) : b = 0 := by sorry
