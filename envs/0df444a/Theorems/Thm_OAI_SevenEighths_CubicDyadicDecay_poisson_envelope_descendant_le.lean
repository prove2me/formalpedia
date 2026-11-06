-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_poisson_envelope_descendant_le
-- name    : OAI.SevenEighths.CubicDyadicDecay.poisson_envelope_descendant_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:01:00.289194+00:00
-- url     : https://prove2.me/theorems/08b51019-c26f-4337-8a4c-a0f159887b17
-- title:
--   Cubic Dyadic Decay: poisson envelope descendant le
-- statement:
--   The Cubic Dyadic Decay construction uses the poisson envelope descendant le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L315-L324
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L315-L324

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

theorem OAI.SevenEighths.CubicDyadicDecay.poisson_envelope_descendant_le (M N e d δ ξ P Q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (N/d)^(3*δ)*(M/e)^(-δ) *
        (P*((M/e)*(N/d))^(2/3 : ℝ) + Q*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)) ≤
      N^(3*δ)*M^(-δ) * (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1)) := by sorry
