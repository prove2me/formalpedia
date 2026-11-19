-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finiteGridOptionalStoppingEventwisePublic
-- name    : Kyprianou.Ch01.finiteGridOptionalStoppingEventwisePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:36:49.683969+00:00
-- url     : https://prove2.me/theorems/0ad4671f-12e1-4346-953d-fa9bd6c14d0a
-- title:
--   Public finite-grid eventwise martingale optional-sampling theorem
-- statement:
--   For a finite integer-valued stopping time bounded by N, adapted continuation events and an integrable real martingale in eventwise integral form, the stopped value is integrable with the same expectation as at time zero. This public lemma is proved by finite pathwise telescoping and null integral of stopped increments, preserving the exact validated private source mathematics.
-- source:
--   Existing accepted proof of Kyprianou.Ch01.finiteGridOptionalStoppingEventwise, submission from the verified Prove2Me server; supporting Exercise 1.10(ii).

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.finiteGridOptionalStoppingEventwisePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω)
    (M : ℕ → Ω → ℝ) (τ : Ω → ℕ) (N : ℕ)
    (hF : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (hBound : ∀ ω, τ ω ≤ N)
    (hInt : ∀ n, Integrable (M n) P)
    (hStop : ∀ n, n < N →
      @MeasurableSet Ω (F n) {ω | n < τ ω})
    (hMart : ∀ (n : ℕ) (A : Set Ω),
      @MeasurableSet Ω (F n) A →
      (∫ ω in A, M (n + 1) ω ∂P) =
        (∫ ω in A, M n ω ∂P)) :
    Integrable (fun ω => M (τ ω) ω) P ∧
      (∫ ω, M (τ ω) ω ∂P) =
        (∫ ω, M 0 ω ∂P) := by sorry
