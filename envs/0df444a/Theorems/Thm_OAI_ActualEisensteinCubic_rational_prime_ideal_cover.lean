-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_rational_prime_ideal_cover
-- name    : OAI.ActualEisensteinCubic.rational_prime_ideal_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:48:01.924286+00:00
-- url     : https://prove2.me/theorems/c9dedfe3-8c7a-4a93-a915-02e2e6413b5f
-- title:
--   Actual Eisenstein Cubic: rational prime ideal cover
-- statement:
--   The Actual Eisenstein Cubic construction uses the rational prime ideal cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L204-L226
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L204-L226

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

theorem OAI.ActualEisensteinCubic.rational_prime_ideal_cover (r : ℕ) (hr : r.Prime) :
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧
      r ≤ qNat a ∧ r ≤ qNat b ∧
      ∀ (Q : Ideal O), Q.IsMaximal → (r : O) ∈ Q →
        Q = Ideal.span {a} ∨ Q = Ideal.span {b} := by sorry
