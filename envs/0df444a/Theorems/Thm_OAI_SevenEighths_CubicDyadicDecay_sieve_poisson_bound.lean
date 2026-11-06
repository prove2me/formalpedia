-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_sieve_poisson_bound
-- name    : OAI.SevenEighths.CubicDyadicDecay.sieve_poisson_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:00:44.838068+00:00
-- url     : https://prove2.me/theorems/771e66e7-f439-497b-89cd-08f44339a3ce
-- title:
--   Cubic Dyadic Decay: sieve poisson bound
-- statement:
--   The Cubic Dyadic Decay construction uses the sieve poisson bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L208-L245
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L208-L245

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

theorem OAI.SevenEighths.CubicDyadicDecay.sieve_poisson_bound (B : ℝ → ℝ) (A M N δ ξ : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    (M/N) * (∑' j : ℕ, B ((2 : ℝ)^j) / (1+M*(2 : ℝ)^j/N^2)^3) ≤
      A*N^(3*δ)*M^(-δ) *
        (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
          decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1)) := by sorry
