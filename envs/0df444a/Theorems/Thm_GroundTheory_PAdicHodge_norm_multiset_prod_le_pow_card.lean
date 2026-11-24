-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_prod_le_pow_card
-- name    : GroundTheory.PAdicHodge.norm_multiset_prod_le_pow_card
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:41.709219+00:00
-- url     : https://prove2.me/theorems/b5e6cfe4-4a3a-499c-be6c-c0b3aa29a6e1
-- title:
--   PAdic Hodge: norm multiset prod le pow card
-- statement:
--   The PAdic Hodge construction uses the norm multiset prod le pow card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L105-L113

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
omit [IsUltrametricDist E]

theorem GroundTheory.PAdicHodge.norm_multiset_prod_le_pow_card {s : Multiset E} {C : ℝ} (h : ∀ a ∈ s, ‖a‖ ≤ C) :
    ‖s.prod‖ ≤ C ^ Multiset.card s := by sorry
