-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_fn_indep
-- name    : GlobalTheory.ThetaSpecialise.fn_indep
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:04:58.811651+00:00
-- url     : https://prove2.me/theorems/fe1a88b9-58b0-4de1-bff9-f7103a31b8d9
-- title:
--   Theta Specialise: fn indep
-- statement:
--   The Theta Specialise construction uses the fn indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMoveMap.lean#L77-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMoveMap.lean#L77-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F} {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]

theorem GlobalTheory.ThetaSpecialise.fn_indep {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → FnOver π U)
    (h : ∑ i, c i • pullFn H.w (le_refl (p ⁻¹ᵁ U)) (a i) = 0) (i : Fin n) : a i = 0 := by sorry
