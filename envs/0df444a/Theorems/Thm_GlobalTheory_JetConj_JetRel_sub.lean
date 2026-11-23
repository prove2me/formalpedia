-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_JetRel_sub
-- name    : GlobalTheory.JetConj.JetRel.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:30.10223+00:00
-- url     : https://prove2.me/theorems/a858c1b7-a07c-4b38-b7b1-fb4d8ba9587f
-- title:
--   Jet Rel: sub
-- statement:
--   The Jet Rel construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L69-L75

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

theorem GlobalTheory.JetConj.JetRel.sub (H : JetRel S f f') (K : JetRel S g g') :
    JetRel S (fun z => f z - g z) (fun z => f' z - g' z) := by sorry
