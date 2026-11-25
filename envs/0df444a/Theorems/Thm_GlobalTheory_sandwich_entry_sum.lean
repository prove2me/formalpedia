-- Prove2me | Theorems.Thm_GlobalTheory_sandwich_entry_sum
-- name    : GlobalTheory.sandwich_entry_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:12.387034+00:00
-- url     : https://prove2.me/theorems/f4ff1af3-3bb7-475c-9839-47ba8cbe2187
-- title:
--   Global Theory: sandwich entry sum
-- statement:
--   The Global Theory construction uses the sandwich entry sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryConjEntryAndInvEntryLinear.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryConjEntryAndInvEntryLinear.lean#L11-L15

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BesselJUnitaryEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryConjEntryAndInvEntryLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset Matrix
open GlobalTheory

theorem GlobalTheory.sandwich_entry_sum {n : Type*} [Fintype n] (A M B : Matrix n n ℂ) (i j : n) :
    (A * M * B) i j = ∑ a, ∑ b, A i a * B b j * M a b := by sorry
