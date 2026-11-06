-- Prove2me | Theorems.Thm_OAI_RankTwoComplex_lattice_gaussian_summable_of_re_bound
-- name    : OAI.RankTwoComplex.lattice_gaussian_summable_of_re_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:42.705191+00:00
-- url     : https://prove2.me/theorems/d9f9bd36-50a0-49a6-94ae-55a744422489
-- title:
--   Rank Two Complex: lattice gaussian summable of re bound
-- statement:
--   The Rank Two Complex construction uses the lattice gaussian summable of re bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L22-L43
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L22-L43

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
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
open OAI.RankTwoComplex
open Real

theorem OAI.RankTwoComplex.lattice_gaussian_summable_of_re_bound (F : ℤ × ℤ → ℂ)
    {eps : ℝ} (heps : 0 < eps)
    (hbound : ∀ z : ℤ × ℤ,
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤ (F z).re) :
    Summable (fun z : ℤ × ℤ => Complex.exp (-(Real.pi : ℂ) * F z)) := by sorry
