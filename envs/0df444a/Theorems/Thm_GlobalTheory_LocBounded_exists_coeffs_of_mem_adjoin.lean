-- Prove2me | Theorems.Thm_GlobalTheory_LocBounded_exists_coeffs_of_mem_adjoin
-- name    : GlobalTheory.LocBounded.exists_coeffs_of_mem_adjoin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:35.557039+00:00
-- url     : https://prove2.me/theorems/493a7966-5a63-4d99-9d9f-d9cf20d6d2e9
-- title:
--   Loc Bounded: exists coeffs of mem adjoin
-- statement:
--   The Loc Bounded construction uses the exists coeffs of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L53-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L53-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded

theorem GlobalTheory.LocBounded.exists_coeffs_of_mem_adjoin {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K)
    {g : Matrix (Fin n) (Fin n) K} (hg : g ∈ Algebra.adjoin K {N}) :
    ∃ c : Fin n → K, g = ∑ k, c k • N ^ (k : ℕ) := by sorry
