-- Prove2me | Theorems.Thm_GlobalTheory_QSA_sqOpen_and_nhdsNE_zero_neBot_adicCompletion
-- name    : GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:04:00.551545+00:00
-- url     : https://prove2.me/theorems/246fc1fe-7513-4df1-a3be-1e3bd373b6d3
-- title:
--   QSA: sq Open and nhds NE zero ne Bot adic Completion
-- statement:
--   The QSA construction uses the sq Open and nhds NE zero ne Bot adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquaringOpenAtOneAdicCompletionNumberField.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquaringOpenAtOneAdicCompletionNumberField.lean#L11-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneOfCompleteTwoNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneAdicCompletionNumberField
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
noncomputable section
open GlobalTheory GlobalTheory.QSA

theorem GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by sorry
