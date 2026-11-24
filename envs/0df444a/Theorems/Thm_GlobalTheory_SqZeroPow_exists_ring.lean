-- Prove2me | Theorems.Thm_GlobalTheory_SqZeroPow_exists_ring
-- name    : GlobalTheory.SqZeroPow.exists_ring
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:25:16.813193+00:00
-- url     : https://prove2.me/theorems/83b206ca-b98e-4b6b-bf3c-ad296539dfce
-- title:
--   Sq Zero Pow: exists ring
-- statement:
--   The Sq Zero Pow construction uses the exists ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean#L22-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean#L22-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRingSqZeroNilpotentAugmented
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SqZeroPow

theorem GlobalTheory.SqZeroPow.exists_ring (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ) (hm : 0 < m) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B),
      (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧
      x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by sorry
