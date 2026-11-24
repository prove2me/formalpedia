-- Prove2me | Theorems.Thm_GlobalTheory_SS_GenProj_exists_openImmersion
-- name    : GlobalTheory.SS.GenProj.exists_openImmersion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:59.742788+00:00
-- url     : https://prove2.me/theorems/b52f2df4-cdee-486e-afde-68643d8bc606
-- title:
--   Gen Proj: exists open Immersion
-- statement:
--   The Gen Proj construction uses the exists open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GenericIsomorphismProductModels.lean#L66-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GenericIsomorphismProductModels.lean#L66-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GenProj

theorem GlobalTheory.SS.GenProj.exists_openImmersion {U X X' : Scheme.{0}} (p : U ⟶ X) (q : U ⟶ X') [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q]
    (H : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p = b ≫ p ↔ a ≫ q = b ≫ q) :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme) (h : V.toScheme ⟶ X'), p' ≫ V.ι = p ∧ Flat p' ∧ Surjective p' ∧
      p' ≫ h = q ∧ IsOpenImmersion h := by sorry
