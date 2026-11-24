-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobSub_isMonHom_pow
-- name    : GlobalTheory.SS.FrobSub.isMonHom_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:34:13.333792+00:00
-- url     : https://prove2.me/theorems/fc109d65-898d-4654-9a98-ed4ad13ea9c5
-- title:
--   Frob Sub: is Mon Hom pow
-- statement:
--   The Frob Sub construction uses the is Mon Hom pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGPowAndClosedSubgroup.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGPowAndClosedSubgroup.lean#L78-L84

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

theorem GlobalTheory.SS.FrobSub.isMonHom_pow {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G)
    (h : IsMonHom (show G ⟶ G from F)) (m : ℕ) : IsMonHom (show G ⟶ G from F ^ m) := by sorry
