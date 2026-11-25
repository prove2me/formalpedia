-- Prove2me | Theorems.Thm_GlobalTheory_HlCoc_pow_fst_of_fixed
-- name    : GlobalTheory.HlCoc.pow_fst_of_fixed
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:29.127593+00:00
-- url     : https://prove2.me/theorems/d0b10795-d6ae-4a3f-8f1c-59a59a68ea84
-- title:
--   Hl Coc: pow fst of fixed
-- statement:
--   The Hl Coc construction uses the pow fst of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueCocycle.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueCocycle.lean#L39-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HlCoc
open Topology
variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]

theorem GlobalTheory.HlCoc.pow_fst_of_fixed (p : SD M G) (h : p.2 • p.1 = p.1) (n : ℕ) :
    (p ^ n).1 = n • p.1 := by sorry
