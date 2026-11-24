-- Prove2me | Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_compact
-- name    : GlobalTheory.entire_apply_eq_of_periodic_of_compact
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:24.338829+00:00
-- url     : https://prove2.me/theorems/920c4e7e-9c9b-42b1-94d9-7e80de6c70dd
-- title:
--   Global Theory: entire apply eq of periodic of compact
-- statement:
--   The Global Theory construction uses the entire apply eq of periodic of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L20-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.entire_apply_eq_of_periodic_of_compact {F : E → V} (hF : Differentiable ℂ F)
    {G K : Set E} (hK : IsCompact K) (hcov : ∀ x, ∃ k ∈ K, ∃ g ∈ G, x = k + g)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) (z w : E) : F z = F w := by sorry
