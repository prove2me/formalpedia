-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finite_sum_special_negative_formula
-- name    : FourierJacobi.Algebra.finite_sum_special_negative_formula
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:19:41.424977+00:00
-- url     : https://prove2.me/theorems/a800804f-ff9e-4d5e-8ca5-d033f686f7df
-- title:
--   Algebra: finite sum special negative formula
-- statement:
--   The Algebra construction uses the finite sum special negative formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/FiniteCalculation.lean#L75-L85
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/FiniteCalculation.lean#L75-L85

import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]

theorem FourierJacobi.Algebra.finite_sum_special_negative_formula (q t a b : K)
    (h : FiniteRegular t a b (-t))
    (ht₀ : t ≠ 0) (hc : poincare t ≠ 0) (hp : satakeNumerator a b ≠ 0)
    (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hf : fourFactors a b (-t ^ 2) ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    (2 / (q + 1) * finiteCore t a b (-t)) * specialNormalizer t a b (-1) =
      2 / (q + 1) := by sorry
