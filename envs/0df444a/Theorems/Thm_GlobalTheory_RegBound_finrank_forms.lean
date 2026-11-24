-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_finrank_forms
-- name    : GlobalTheory.RegBound.finrank_forms
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:20:10.153291+00:00
-- url     : https://prove2.me/theorems/87110a9d-3e5f-43c5-b8e8-9af650c18ddb
-- title:
--   Reg Bound: finrank forms
-- statement:
--   The Reg Bound construction uses the finrank forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L247-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L247-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]

theorem GlobalTheory.RegBound.finrank_forms (e : ℕ) : finrank K (homogeneousSubmodule σ K e) = nmon σ e := by sorry
