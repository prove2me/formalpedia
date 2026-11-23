-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_JetRel_mul
-- name    : GlobalTheory.JetConj.JetRel.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:11.392955+00:00
-- url     : https://prove2.me/theorems/fcdafce6-03e0-45f7-9b82-a8aa99690d5b
-- title:
--   Jet Rel: mul
-- statement:
--   The Jet Rel construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L85-L89

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

theorem GlobalTheory.JetConj.JetRel.mul (H : JetRel S f f') (K : JetRel S g g') :
    JetRel S (fun z => f z * g z) (fun z => f' z * g' z) := by sorry
