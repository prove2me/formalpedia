-- Prove2me | Theorems.Thm_GlobalTheory_HL_GoodClass_unit_entries
-- name    : GlobalTheory.HL.GoodClass.unit_entries
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:54.063717+00:00
-- url     : https://prove2.me/theorems/22a275ca-c84a-50f5-afdc-14792028dcd2
-- title:
--   Good Class: unit entries
-- statement:
--   The Good Class construction uses the unit entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitEntries.lean#L212-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitEntries.lean#L212-L249

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
open GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]

theorem GlobalTheory.HL.GoodClass.unit_entries (O : Subring E) (hO : ∀ (x : E) (s : ℕ), 0 < s → x ^ s ∈ O → x ∈ O) :
    ∀ bs : List (Eˣ × ℕ+), (∀ l ≤ (bs.map (fun b => (b.2 : ℕ))).sum, (∀ a < l, sig bs a < l) →
      UnitIn O (∏ a ∈ Finset.range l, ptEntryL bs a (sig bs a))) →
      ∀ a < (bs.map (fun b => (b.2 : ℕ))).sum, UnitIn O (ptEntryL bs a (sig bs a))
  := by sorry
