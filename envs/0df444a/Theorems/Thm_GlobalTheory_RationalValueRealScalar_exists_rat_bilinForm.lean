-- Prove2me | Theorems.Thm_GlobalTheory_RationalValueRealScalar_exists_rat_bilinForm
-- name    : GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:44.243673+00:00
-- url     : https://prove2.me/theorems/ea6c9e4b-20b5-5cd3-81f7-8643f992e9d6
-- title:
--   Rational Value Real Scalar: exists rat bilin Form
-- statement:
--   The Rational Value Real Scalar construction uses the exists rat bilin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRatBilinForm.lean#L34-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRatBilinForm.lean#L34-L56

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

theorem GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v : V, ((B u v : ℚ) : ℝ) = -(om (p u) (p v)) := by sorry
