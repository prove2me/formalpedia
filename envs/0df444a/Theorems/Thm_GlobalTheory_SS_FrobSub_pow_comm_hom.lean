-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobSub_pow_comm_hom
-- name    : GlobalTheory.SS.FrobSub.pow_comm_hom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:33:28.066122+00:00
-- url     : https://prove2.me/theorems/f57af910-e49b-4664-9535-7f4f7fc75003
-- title:
--   Frob Sub: pow comm hom
-- statement:
--   The Frob Sub construction uses the pow comm hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGPowAndClosedSubgroup.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGPowAndClosedSubgroup.lean#L69-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGPowAndClosedSubgroup
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobSub

theorem GlobalTheory.SS.FrobSub.pow_comm_hom {C : Type*} [Category C] {N G : C} (ν : N ⟶ G) (F : End G) (F' : End N)
    (h : (show N ⟶ N from F') ≫ ν = ν ≫ (show G ⟶ G from F)) (m : ℕ) :
    (show N ⟶ N from F' ^ m) ≫ ν = ν ≫ (show G ⟶ G from F ^ m) := by sorry
