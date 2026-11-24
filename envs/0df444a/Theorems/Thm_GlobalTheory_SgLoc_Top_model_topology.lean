-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_Top_model_topology
-- name    : GlobalTheory.SgLoc.Top.model_topology
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:10:08.695921+00:00
-- url     : https://prove2.me/theorems/33dafc5c-5870-46ff-b7a3-f8fd78af01fe
-- title:
--   Top: model topology
-- statement:
--   The Top construction uses the model topology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L279-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L279-L298

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [MeasurableSpace E]

theorem GlobalTheory.SgLoc.Top.model_topology : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type}
    [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
    IsTopologicalRing E ∧ T2Space E ∧ LocallyCompactSpace E ∧ SecondCountableTopology E ∧
    ContinuousSMul F E ∧ IsCompact (M.R : Set E) ∧ IsOpen (M.R : Set E) ∧
    IsCompact (M.L.O : Set E) ∧ IsOpen (M.L.O : Set E) ∧ M.R ≤ M.L.O := by sorry
