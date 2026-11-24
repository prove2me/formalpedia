-- Prove2me | Theorems.Thm_GlobalTheory_SS_CompatCrit_exists_model
-- name    : GlobalTheory.SS.CompatCrit.exists_model
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:46.645776+00:00
-- url     : https://prove2.me/theorems/c3259445-9036-4496-be2f-aa128993702b
-- title:
--   Compat Crit: exists model
-- statement:
--   The Compat Crit construction uses the exists model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenImmersionOfSections.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenImmersionOfSections.lean#L55-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.CompatCrit
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem GlobalTheory.SS.CompatCrit.exists_model (M : Model R A) {G : Scheme.{0}} (p : G ⟶ M.Y.left) [IsOpenImmersion p]
    [QuasiCompact p] (i : A.left ⟶ G) (hi : i ≫ p = M.j) :
    ∃ e : (Over.pullback (spMap (algebraMap R K))).obj (Over.mk (p ≫ M.Y.hom)) ≅ A,
      e.inv.left ≫ pullback.fst (p ≫ M.Y.hom) (spMap (algebraMap R K)) = i := by sorry
