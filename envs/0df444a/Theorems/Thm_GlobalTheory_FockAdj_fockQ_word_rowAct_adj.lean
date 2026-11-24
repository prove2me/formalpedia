-- Prove2me | Theorems.Thm_GlobalTheory_FockAdj_fockQ_word_rowAct_adj
-- name    : GlobalTheory.FockAdj.fockQ_word_rowAct_adj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:47.470589+00:00
-- url     : https://prove2.me/theorems/e7a824f9-9efe-4d01-82b7-38585d6674d8
-- title:
--   Fock Adj: fock Q word row Act adj
-- statement:
--   The Fock Adj construction uses the fock Q word row Act adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FockQWordRowActAdj.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FockQWordRowActAdj.lean#L41-L42

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FockQWordRowActAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open GlobalTheory GlobalTheory.FockAdj

theorem GlobalTheory.FockAdj.fockQ_word_rowAct_adj : Formalism.GradedWeylDivisibility.FockQWordAdj ∧ Formalism.GradedWeylDivisibility.FockQRowAct := by sorry
