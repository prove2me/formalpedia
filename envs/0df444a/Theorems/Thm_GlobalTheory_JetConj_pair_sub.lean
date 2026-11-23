-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_pair_sub
-- name    : GlobalTheory.JetConj.pair_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:22.214874+00:00
-- url     : https://prove2.me/theorems/ae1f740f-19a1-43ef-98ce-a06a49941d3e
-- title:
--   Jet Conj: pair sub
-- statement:
--   The Jet Conj construction uses the pair sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L46-L46

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

theorem GlobalTheory.JetConj.pair_sub {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a - c, b - d) ∈ S := by sorry
