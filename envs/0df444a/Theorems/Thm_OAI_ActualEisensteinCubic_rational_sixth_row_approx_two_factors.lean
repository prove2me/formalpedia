-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_rational_sixth_row_approx_two_factors
-- name    : OAI.ActualEisensteinCubic.rational_sixth_row_approx_two_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:47:56.365198+00:00
-- url     : https://prove2.me/theorems/e3c9fa1d-8377-4e4e-84a3-5358516c39d4
-- title:
--   Actual Eisenstein Cubic: rational sixth row approx two factors
-- statement:
--   The Actual Eisenstein Cubic construction uses the rational sixth row approx two factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L56-L107
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L56-L107

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

theorem OAI.ActualEisensteinCubic.rational_sixth_row_approx_two_factors
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (r a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (D : ℕ)
    (hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, r ∈ P i) → a ∣ n ∨ b ∣ n)
    (hcolnorm : ∀ n ∈ columns, qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (r ^ 6))‖ ≤
      (64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) : ℕ) := by sorry
