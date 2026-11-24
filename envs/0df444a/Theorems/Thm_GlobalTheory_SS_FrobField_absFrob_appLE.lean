-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobField_absFrob_appLE
-- name    : GlobalTheory.SS.FrobField.absFrob_appLE
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:33:55.381309+00:00
-- url     : https://prove2.me/theorems/2a71035c-4742-4460-a814-fe75c52dad2b
-- title:
--   Frob Field: abs Frob app LE
-- statement:
--   The Frob Field construction uses the abs Frob app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L54-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField

theorem GlobalTheory.SS.FrobField.absFrob_appLE (X : Scheme.{0}) (p r : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens)
    (e : U ≤ absFrob X p r hp h ⁻¹ᵁ U) (f : Γ(X, U)) :
    ((absFrob X p r hp h).appLE U U e).hom f = f ^ p ^ r := by sorry
