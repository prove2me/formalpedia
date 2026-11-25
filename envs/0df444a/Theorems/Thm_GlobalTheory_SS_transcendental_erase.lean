-- Prove2me | Theorems.Thm_GlobalTheory_SS_transcendental_erase
-- name    : GlobalTheory.SS.transcendental_erase
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:42:52.21454+00:00
-- url     : https://prove2.me/theorems/eff42ae7-b8e0-4b8e-8b4d-07e6611ed8ee
-- title:
--   SS: transcendental erase
-- statement:
--   The SS construction uses the transcendental erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesOfFgField.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesOfFgField.lean#L60-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgField
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
open GlobalTheory GlobalTheory.SS

theorem GlobalTheory.SS.transcendental_erase {k K : Type} [Field k] [Field K] [Algebra k K] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K)) (t : s) :
    Transcendental (IntermediateField.adjoin k (s \ {(t : K)})) (t : K) := by sorry
