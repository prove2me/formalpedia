-- Prove2me | Theorems.Thm_GlobalTheory_GlobalFunctions_appTop_comp_eq
-- name    : GlobalTheory.GlobalFunctions.appTop_comp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:21.774721+00:00
-- url     : https://prove2.me/theorems/6d669429-0407-4d67-a37c-4541ff60b5bd
-- title:
--   Global Functions: app Top comp eq
-- statement:
--   The Global Functions construction uses the app Top comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L125-L128

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
variable {R B C : CommRingCat.{0}} {X : Scheme.{0}}

theorem GlobalTheory.GlobalFunctions.appTop_comp_eq {p : X ⟶ Spec R} {i : Spec B ⟶ X} {φ : R ⟶ B}
    (hφ : i ≫ p = Spec.map φ) :
    p.appTop ≫ i.appTop ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso R).hom ≫ φ := by sorry
