-- Prove2me | Theorems.Thm_GlobalTheory_PrimeRecip_table_ok
-- name    : GlobalTheory.PrimeRecip.table_ok
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:49:08.533735+00:00
-- url     : https://prove2.me/theorems/a42f1e50-b48f-423a-bd67-78547dc10a18
-- title:
--   Prime Recip: table ok
-- statement:
--   The Prime Recip construction uses the table ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L301-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L301-L301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open GlobalTheory GlobalTheory.PrimeRecip

theorem GlobalTheory.PrimeRecip.table_ok : okAll 100 table 16900 = true := by sorry
