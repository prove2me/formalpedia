-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_matrix_of_pow_bounded
-- name    : GlobalTheory.isIntegral_matrix_of_pow_bounded
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:54.811031+00:00
-- url     : https://prove2.me/theorems/740edc40-7023-4065-a9bd-767bc7752c16
-- title:
--   Global Theory: is Integral matrix of pow bounded
-- statement:
--   The Global Theory construction uses the is Integral matrix of pow bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfIsCompactClosureZpowers.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfIsCompactClosureZpowers.lean#L8-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsCompactClosureZpowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
open NumberField IsDedekindDomain

theorem GlobalTheory.isIntegral_matrix_of_pow_bounded {O K : Type} [CommRing O] [IsNoetherianRing O]
    [Field K] [Algebra O K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ (k : ℕ) (i j : Fin n), ∃ b : O, algebraMap O K b = a * (g ^ k) i j) :
    IsIntegral O g := by sorry
