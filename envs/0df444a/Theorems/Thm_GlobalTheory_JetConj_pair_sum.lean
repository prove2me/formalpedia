-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_pair_sum
-- name    : GlobalTheory.JetConj.pair_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:23.160664+00:00
-- url     : https://prove2.me/theorems/f7655269-9f02-49f3-be3a-d6261d9acd2d
-- title:
--   Jet Conj: pair sum
-- statement:
--   The Jet Conj construction uses the pair sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L48-L52

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

theorem GlobalTheory.JetConj.pair_sum {ι : Type*} (s : Finset ι) {a b : ι → ℂ} (h : ∀ i ∈ s, (a i, b i) ∈ S) :
    (∑ i ∈ s, a i, ∑ i ∈ s, b i) ∈ S := by sorry
