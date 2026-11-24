-- Prove2me | Theorems.Thm_GlobalTheory_flat_closure_subgroup
-- name    : GlobalTheory.flat_closure_subgroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:52:00.190305+00:00
-- url     : https://prove2.me/theorems/0358c58b-a391-422e-9849-3b834feab482
-- title:
--   Global Theory: flat closure subgroup
-- statement:
--   The Global Theory construction uses the flat closure subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean#L98-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.flat_closure_subgroup :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (P Ga : Over (Sp T)) [GrpObj P] (io : Ga ⟶ P) (Z : Over (Sp K)) [GrpObj Z] (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj P) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left → Flat Ga.hom → IsMonHom i → e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io → ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by sorry
