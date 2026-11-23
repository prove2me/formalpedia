-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_pair_natCast
-- name    : GlobalTheory.JetConj.pair_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:11.745114+00:00
-- url     : https://prove2.me/theorems/3fbb540a-bc5f-4564-adf8-5433697d72f6
-- title:
--   Jet Conj: pair nat Cast
-- statement:
--   The Jet Conj construction uses the pair nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L38-L40

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

theorem GlobalTheory.JetConj.pair_natCast (S : Subring (ℂ × ℂ)) (n : ℕ) : ((n : ℂ), (n : ℂ)) ∈ S := by sorry
