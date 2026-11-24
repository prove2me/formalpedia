-- Prove2me | Theorems.Thm_GlobalTheory_PhiBase_exists_pull_sec
-- name    : GlobalTheory.PhiBase.exists_pull_sec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:16.549078+00:00
-- url     : https://prove2.me/theorems/dd26675c-5b9c-4c72-90df-cf60d2e16528
-- title:
--   Phi Base: exists pull sec
-- statement:
--   The Phi Base construction uses the exists pull sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AbelianPartEqOfThetaOperatorEq.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AbelianPartEqOfThetaOperatorEq.lean#L20-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOfIsGenTransl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsThetaPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AbelianPartEqOfThetaOperatorEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PhiBase

theorem GlobalTheory.PhiBase.exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (t : Y' ⟶ Y) (g : Y' ⟶ X)
    (hg : t ≫ f = g) (θ : LB.Sec (L.pull f)) : ∃ θ' : LB.Sec (L.pull g),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
        sval (L := L) (φ := fun _ : PUnit => g) (ε := fun _ => 1) θ' r z J =
          sval (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ (r ≫ t) z J := by sorry
