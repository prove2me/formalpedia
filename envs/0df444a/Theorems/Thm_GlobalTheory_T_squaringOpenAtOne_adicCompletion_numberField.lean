-- Prove2me | Theorems.Thm_GlobalTheory_T_squaringOpenAtOne_adicCompletion_numberField
-- name    : GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:53.856283+00:00
-- url     : https://prove2.me/theorems/458a7fbf-02aa-4d3a-b45f-1c0a70c2f376
-- title:
--   T: squaring Open At One adic Completion number Field
-- statement:
--   The T construction uses the squaring Open At One adic Completion number Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquaringOpenAtOneAdicCompletionNumberFieldStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquaringOpenAtOneAdicCompletionNumberFieldStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneAdicCompletionNumberField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneAdicCompletionNumberFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by sorry
