-- Prove2me | Theorems.Thm_GlobalTheory_RationalValueRealScalar_exists_rat_value
-- name    : GlobalTheory.RationalValueRealScalar.exists_rat_value
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:15:23.78902+00:00
-- url     : https://prove2.me/theorems/5db01584-dbf4-41d3-91c3-1f136095738b
-- title:
--   Rational Value Real Scalar: exists rat value
-- statement:
--   The Rational Value Real Scalar construction uses the exists rat value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRatBilinForm.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRatBilinForm.lean#L19-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRatBilinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RationalValueRealScalar

theorem GlobalTheory.RationalValueRealScalar.exists_rat_value {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) (u v : V) :
    ∃ q : ℚ, (q : ℝ) = -(om (p u) (p v)) := by sorry
