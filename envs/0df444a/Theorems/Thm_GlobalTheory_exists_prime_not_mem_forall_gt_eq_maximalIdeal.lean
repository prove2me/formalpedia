-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_not_mem_forall_gt_eq_maximalIdeal
-- name    : GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:20.129253+00:00
-- url     : https://prove2.me/theorems/8b9fc6e7-8524-4883-b203-7491602b40f5
-- title:
--   Global Theory: exists prime not mem forall gt eq maximal Ideal
-- statement:
--   The Global Theory construction uses the exists prime not mem forall gt eq maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeNotMemForallGtEqMaximalIdeal.lean#L8-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeNotMemForallGtEqMaximalIdeal.lean#L8-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeNotMemForallGtEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal (C : Type) [CommRing C] [IsDomain C]
    [IsLocalRing C] [IsNoetherianRing C] (x : C) (hx : x ≠ 0) (hxm : x ∈ maximalIdeal C) :
    ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by sorry
