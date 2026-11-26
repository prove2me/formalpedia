-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finite_sum_principal_formula
-- name    : FourierJacobi.Algebra.finite_sum_principal_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:15.375847+00:00
-- url     : https://prove2.me/theorems/c5761176-65bb-439e-a1ed-080102c1ad7a
-- title:
--   Algebra: finite sum principal formula
-- statement:
--   The Algebra construction uses the finite sum principal formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/FiniteCalculation.lean#L60-L73
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/FiniteCalculation.lean#L60-L73

import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]

theorem FourierJacobi.Algebra.finite_sum_principal_formula (q t a b d : K)
    (h : FiniteRegular t a b d)
    (hc : poincare t ≠ 0) (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hd₁ : d₁ t a b d ≠ 0) (hd₂ : d₂ t a b d ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0)
    (hm : 1 - d * t ≠ 0) (hp : 1 + d * t ≠ 0)
    (him : 1 - t / d ≠ 0) (hip : 1 + t / d ≠ 0) :
    (2 / (q + 1) * finiteCore t a b d) * principalNormalizer t a b d =
      2 / (q + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * t) * (1 + t / d)) := by sorry
