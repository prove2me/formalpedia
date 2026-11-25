-- Prove2me | Theorems.Thm_GlobalTheory_exists_gen_of_rigidified_of_flat_baseChange
-- name    : GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:40.230857+00:00
-- url     : https://prove2.me/theorems/e244d511-b971-4865-974d-e31fbde3fe8d
-- title:
--   Global Theory: exists gen of rigidified of flat base Change
-- statement:
--   The Global Theory construction uses the exists gen of rigidified of flat base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigidifiedFaithfullyFlatDescent.lean#L157-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigidifiedFaithfullyFlatDescent.lean#L157-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigidifiedFaithfullyFlatDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory

theorem GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange :
    Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by sorry
