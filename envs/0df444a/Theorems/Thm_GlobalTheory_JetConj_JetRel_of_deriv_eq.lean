-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_JetRel_of_deriv_eq
-- name    : GlobalTheory.JetConj.JetRel.of_deriv_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:38.281132+00:00
-- url     : https://prove2.me/theorems/a988d759-c858-40c0-a48a-845a09de839e
-- title:
--   Jet Rel: of deriv eq
-- statement:
--   The Jet Rel construction uses the of deriv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L175-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L175-L186

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

theorem GlobalTheory.JetConj.JetRel.of_deriv_eq (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) (G : JetRel S g g')
    (e : _root_.deriv f =ᶠ[𝓝 0] fun z => f z * g z) (e' : _root_.deriv f' =ᶠ[𝓝 0] fun z => f' z * g' z)
    (h0 : (f 0, f' 0) ∈ S) : JetRel S f f' := by sorry
