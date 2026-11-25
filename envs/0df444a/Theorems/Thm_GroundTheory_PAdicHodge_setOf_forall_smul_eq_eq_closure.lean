-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_setOf_forall_smul_eq_eq_closure
-- name    : GroundTheory.PAdicHodge.setOf_forall_smul_eq_eq_closure
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:28:51.09804+00:00
-- url     : https://prove2.me/theorems/f705abff-67da-449b-886d-d3a677374681
-- title:
--   PAdic Hodge: set Of forall smul eq eq closure
-- statement:
--   The PAdic Hodge construction uses the set Of forall smul eq eq closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L472-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L472-L505

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.setOf_forall_smul_eq_eq_closure (S : Set Gal(PadicAlgCl p/K)) (L : Set (PadicAlgCl p))
    (hL : ∀ y ∈ L, ∀ σ ∈ S, σ y = y) {C : ℝ} (hC : 0 < C)
    (hax : ∀ z : PadicAlgCl p, ∀ r : ℝ, (∀ σ ∈ S, ‖σ z - z‖ ≤ r) → ∃ y ∈ L, ‖z - y‖ ≤ C * r) :
    {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} = closure (((↑) : PadicAlgCl p → ℂ_[p]) '' L) := by sorry
