-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_invariant
-- name    : GlobalTheory.WeilM.HaarUniq.exists_invariant
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:48:21.418+00:00
-- url     : https://prove2.me/theorems/6e4bd97d-2a3a-48ec-880a-cc2637dac96f
-- title:
--   Haar Uniq: exists invariant
-- statement:
--   The Haar Uniq construction uses the exists invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L38-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L38-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

theorem GlobalTheory.WeilM.HaarUniq.exists_invariant [NonarchimedeanAddGroup V] {φ : V → ℂ}
    (hφ : φ ∈ _root_.GlobalTheory.WeilM.SB V) :
    ∃ K : OpenAddSubgroup V, ∀ k ∈ K, ∀ x, φ (x + k) = φ x := by sorry
