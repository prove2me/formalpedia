-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_JetRel_of_pow
-- name    : GlobalTheory.JetConj.JetRel.of_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:40:10.673867+00:00
-- url     : https://prove2.me/theorems/e6340221-fc2f-4de5-99d2-a07619ef881f
-- title:
--   Jet Rel: of pow
-- statement:
--   The Jet Rel construction uses the of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L207-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L207-L219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}

theorem GlobalTheory.JetConj.JetRel.of_pow (hS : IsFieldGraph S) (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) {k : ℕ}
    (hk : k ≠ 0) (H : JetRel S (fun z => f z ^ k) (fun z => f' z ^ k)) (h0 : (f 0, f' 0) ∈ S)
    (hne : f 0 ≠ 0) : JetRel S f f' := by sorry
