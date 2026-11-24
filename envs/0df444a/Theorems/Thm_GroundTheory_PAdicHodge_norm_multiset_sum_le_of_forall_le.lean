-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_sum_le_of_forall_le
-- name    : GroundTheory.PAdicHodge.norm_multiset_sum_le_of_forall_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:29:08.814489+00:00
-- url     : https://prove2.me/theorems/db57cddd-5589-4801-9865-9ad5d0e2a837
-- title:
--   PAdic Hodge: norm multiset sum le of forall le
-- statement:
--   The PAdic Hodge construction uses the norm multiset sum le of forall le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L93-L101

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
variable {E : Type*} [NormedField E] [IsUltrametricDist E]

theorem GroundTheory.PAdicHodge.norm_multiset_sum_le_of_forall_le {s : Multiset E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a ∈ s, ‖a‖ ≤ C) : ‖s.sum‖ ≤ C := by sorry
