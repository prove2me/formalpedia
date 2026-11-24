-- Prove2me | Theorems.Thm_GlobalTheory_SS_GenProj_exists_image
-- name    : GlobalTheory.SS.GenProj.exists_image
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:33:25.52008+00:00
-- url     : https://prove2.me/theorems/e5ea7811-1b16-44b2-9065-26c8094a8b8b
-- title:
--   Gen Proj: exists image
-- statement:
--   The Gen Proj construction uses the exists image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GenericIsomorphismProductModels.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GenericIsomorphismProductModels.lean#L52-L64

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

theorem GlobalTheory.SS.GenProj.exists_image {U X : Scheme.{0}} (p : U ⟶ X) [Flat p] [LocallyOfFinitePresentation p] :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme), p' ≫ V.ι = p ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' := by sorry
