-- Prove2me | Theorems.Thm_GlobalTheory_SeriesNakayama_mem_pow_smul_top_iff
-- name    : GlobalTheory.SeriesNakayama.mem_pow_smul_top_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:30.220537+00:00
-- url     : https://prove2.me/theorems/88739cf7-62b8-4c3e-9a76-a2b764ac9220
-- title:
--   Series Nakayama: mem pow smul top iff
-- statement:
--   The Series Nakayama construction uses the mem pow smul top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L8-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama

theorem GlobalTheory.SeriesNakayama.mem_pow_smul_top_iff {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (π : O)
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O M) ↔ ∃ y : M, π ^ n • y = x := by sorry
