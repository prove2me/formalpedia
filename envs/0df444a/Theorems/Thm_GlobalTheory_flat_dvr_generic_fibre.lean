-- Prove2me | Theorems.Thm_GlobalTheory_flat_dvr_generic_fibre
-- name    : GlobalTheory.flat_dvr_generic_fibre
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:52:00.244722+00:00
-- url     : https://prove2.me/theorems/a3311fcb-b59c-40e2-a24c-1d9ea9bfc9fc
-- title:
--   Global Theory: flat dvr generic fibre
-- statement:
--   The Global Theory construction uses the flat dvr generic fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L128-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L128-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
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

theorem GlobalTheory.flat_dvr_generic_fibre :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X : Over (Sp T)), Flat Y.hom → IsSeparated X.hom → ∀ a b : Y ⟶ X, (Over.pullback (spMap (algebraMap T K))).map a = (Over.pullback (spMap (algebraMap T K))).map b → a = b) ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X Ga : Over (Sp T)) (io : Ga ⟶ X) (a : Y ⟶ X) (a' : (Over.pullback (spMap (algebraMap T K))).obj Y ⟶ (Over.pullback (spMap (algebraMap T K))).obj Ga), Flat Y.hom → IsClosedImmersion io.left → a' ≫ (Over.pullback (spMap (algebraMap T K))).map io = (Over.pullback (spMap (algebraMap T K))).map a → ∃! b : Y ⟶ Ga, b ≫ io = a ∧ (Over.pullback (spMap (algebraMap T K))).map b = a') ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'] (F : G ⟶ G'), Flat G.hom → IsSeparated G'.hom → IsMonHom ((Over.pullback (spMap (algebraMap T K))).map F) → IsMonHom F) := by sorry
