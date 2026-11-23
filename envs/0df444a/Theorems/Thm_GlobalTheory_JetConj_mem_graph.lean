-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_mem_graph
-- name    : GlobalTheory.JetConj.mem_graph
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:02.501178+00:00
-- url     : https://prove2.me/theorems/5648b70a-241e-4449-91d2-11a0d96d3c6a
-- title:
--   Jet Conj: mem graph
-- statement:
--   The Jet Conj construction uses the mem graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L16-L24

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

theorem GlobalTheory.JetConj.mem_graph {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {a b : ℂ} :
    (a, b) ∈ graph M ρ ↔ ∃ h : a ∈ M, ρ ⟨a, h⟩ = b := by sorry
