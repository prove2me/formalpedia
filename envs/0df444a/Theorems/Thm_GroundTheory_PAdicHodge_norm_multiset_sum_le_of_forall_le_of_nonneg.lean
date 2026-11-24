-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_sum_le_of_forall_le_of_nonneg
-- name    : GroundTheory.PAdicHodge.norm_multiset_sum_le_of_forall_le_of_nonneg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:10.820309+00:00
-- url     : https://prove2.me/theorems/8e4c2872-e40d-429d-857f-735a5a8f6ec4
-- title:
--   PAdic Hodge: norm multiset sum le of forall le of nonneg
-- statement:
--   The PAdic Hodge construction uses the norm multiset sum le of forall le of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L297-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L297-L304

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
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
open Polynomial Module IntermediateField
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.norm_multiset_sum_le_of_forall_le_of_nonneg (s : Multiset (PadicAlgCl p)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ s, ‖x‖ ≤ C) : ‖s.sum‖ ≤ C := by sorry
