-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_orthogonal_fin
-- name    : GroundTheory.PAdicHodge.exists_orthogonal_fin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:35.665187+00:00
-- url     : https://prove2.me/theorems/3b41e276-2cb2-4a56-b1ec-eeb2f17baa65
-- title:
--   PAdic Hodge: exists orthogonal fin
-- statement:
--   The PAdic Hodge construction uses the exists orthogonal fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean#L53-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean#L53-L128

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]
variable [CompleteSpace k]

theorem GroundTheory.PAdicHodge.exists_orthogonal_fin (n : ℕ) : ∀ (v : Fin n → E), LinearIndependent k v →
    ∀ {τ : ℝ}, 0 < τ → τ < 1 →
    ∃ w : Fin n → E, (∀ i, w i ≠ 0) ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : Fin n → k) (i : Fin n), τ * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by sorry
