-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_sieve_growth_majorant
-- name    : OAI.SevenEighths.CubicDyadicDecay.sieve_growth_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:12.054326+00:00
-- url     : https://prove2.me/theorems/c6a86de3-0de8-4cc9-919e-5705c4c8f1d0
-- title:
--   Cubic Dyadic Decay: sieve growth majorant
-- statement:
--   The Cubic Dyadic Decay construction uses the sieve growth majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L168-L186
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L168-L186

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

theorem OAI.SevenEighths.CubicDyadicDecay.sieve_growth_majorant (B : ℝ → ℝ) (A N t δ ξ : ℝ)
    (hA : 0 ≤ A) (hN : 0 < N) (ht : 0 < t)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ≤
      A*N^δ * (N*decayConstant (1/3+δ)*t^(-(1/3+δ)) +
        decayConstant (ξ+δ)*t^(-(ξ+δ))) := by sorry
