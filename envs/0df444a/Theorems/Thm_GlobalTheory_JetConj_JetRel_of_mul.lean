-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_JetRel_of_mul
-- name    : GlobalTheory.JetConj.JetRel.of_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:28.287689+00:00
-- url     : https://prove2.me/theorems/38a46584-45ce-45d9-90b6-5cb944e37ea2
-- title:
--   Jet Rel: of mul
-- statement:
--   The Jet Rel construction uses the of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L147-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L147-L173

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

theorem GlobalTheory.JetConj.JetRel.of_mul (hS : IsFieldGraph S) (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0)
    (G : JetRel S g g') (h0 : ¬ g =ᶠ[𝓝 0] 0)
    (H : JetRel S (fun z => f z * g z) (fun z => f' z * g' z)) : JetRel S f f' := by sorry
