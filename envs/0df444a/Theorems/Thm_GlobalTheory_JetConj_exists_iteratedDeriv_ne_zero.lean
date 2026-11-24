-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_exists_iteratedDeriv_ne_zero
-- name    : GlobalTheory.JetConj.exists_iteratedDeriv_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:39:30.689639+00:00
-- url     : https://prove2.me/theorems/2de0e311-b104-414a-84c3-8288a4053b64
-- title:
--   Jet Conj: exists iterated Deriv ne zero
-- statement:
--   The Jet Conj construction uses the exists iterated Deriv ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L119-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L119-L130

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

theorem GlobalTheory.JetConj.exists_iteratedDeriv_ne_zero (hg : AnalyticAt ℂ g 0) (h0 : ¬ g =ᶠ[𝓝 0] 0) :
    ∃ k, iteratedDeriv k g 0 ≠ 0 := by sorry
