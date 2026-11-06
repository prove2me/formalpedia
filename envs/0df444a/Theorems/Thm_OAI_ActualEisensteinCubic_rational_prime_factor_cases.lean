-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_rational_prime_factor_cases
-- name    : OAI.ActualEisensteinCubic.rational_prime_factor_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:48:06.370582+00:00
-- url     : https://prove2.me/theorems/07cbe2d4-a653-413b-87ec-39f8f33430f1
-- title:
--   Actual Eisenstein Cubic: rational prime factor cases
-- statement:
--   The Actual Eisenstein Cubic construction uses the rational prime factor cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L151-L194
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L151-L194

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount

theorem OAI.ActualEisensteinCubic.rational_prime_factor_cases (r : ℕ) (hr : r.Prime) :
    (Ideal.span {(r : O)} : Ideal O).IsMaximal ∨
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧ (r : O) = a * b ∧
      qNat a = r ∧ qNat b = r ∧
      (Ideal.span {a} : Ideal O).IsMaximal ∧
      (Ideal.span {b} : Ideal O).IsMaximal := by sorry
