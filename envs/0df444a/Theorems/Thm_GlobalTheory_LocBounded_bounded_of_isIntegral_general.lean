-- Prove2me | Theorems.Thm_GlobalTheory_LocBounded_bounded_of_isIntegral_general
-- name    : GlobalTheory.LocBounded.bounded_of_isIntegral_general
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:30.575862+00:00
-- url     : https://prove2.me/theorems/3f955ccf-df9d-4e33-ac3a-9c9546d8e451
-- title:
--   Loc Bounded: bounded of is Integral general
-- statement:
--   The Loc Bounded construction uses the bounded of is Integral general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L113-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L113-L196

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

theorem GlobalTheory.LocBounded.bounded_of_isIntegral_general {K Γ O : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [CommRing O] [Algebra O K]
    (hOv : ∀ y : O, v (algebraMap O K y) ≤ 1)
    (hvO : ∀ x : K, v x ≤ 1 → ∃ y : O, algebraMap O K y = x)
    (hint : ∀ x : K, IsIntegral O x → v x ≤ 1)
    {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (hsep : N.charpoly.Separable) :
    ∃ c : Γ, ∀ g ∈ Algebra.adjoin K {N}, IsIntegral O g → ∀ i j, v (g i j) ≤ c := by sorry
