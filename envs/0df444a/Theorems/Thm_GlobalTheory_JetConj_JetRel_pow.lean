-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_JetRel_pow
-- name    : GlobalTheory.JetConj.JetRel.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:36.645809+00:00
-- url     : https://prove2.me/theorems/e88f5d3a-bd47-44d1-9efc-822aad5cadf8
-- title:
--   Jet Rel: pow
-- statement:
--   The Jet Rel construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L91-L94

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

theorem GlobalTheory.JetConj.JetRel.pow (H : JetRel S f f') (k : ℕ) : JetRel S (fun z => f z ^ k) (fun z => f' z ^ k) := by sorry
