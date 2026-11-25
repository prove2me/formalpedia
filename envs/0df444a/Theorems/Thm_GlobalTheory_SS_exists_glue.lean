-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_glue
-- name    : GlobalTheory.SS.exists_glue
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:10.422413+00:00
-- url     : https://prove2.me/theorems/4fbdcdba-b5a8-5344-af78-78ef9e718652
-- title:
--   SS: exists glue
-- statement:
--   The SS construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelExtensionOfDefinedAtPoints.lean#L64-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelExtensionOfDefinedAtPoints.lean#L64-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
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
open GlobalTheory GlobalTheory.SS
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]

theorem GlobalTheory.SS.exists_glue (M : Model R A) (N : Model R A') (f : A ⟶ A') (U : M.Y.left → M.Y.left.Opens)
    (g : ∀ y, (U y).toScheme ⟶ N.Y.left) (hU : ∀ y, y ∈ U y) (hg : ∀ y, Extends M N f (U y) (g y)) :
    ∃ G : M.Y ⟶ N.Y, M.j ≫ G.left = f.left ≫ N.j ∧ ∀ y, (U y).ι ≫ G.left = g y := by sorry
