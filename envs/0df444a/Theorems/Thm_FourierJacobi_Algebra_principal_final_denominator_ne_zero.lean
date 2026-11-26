-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_principal_final_denominator_ne_zero
-- name    : FourierJacobi.Algebra.principal_final_denominator_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:43:29.152378+00:00
-- url     : https://prove2.me/theorems/351a0d82-1dd2-50bf-9664-afb1d55e1447
-- title:
--   Algebra: principal final denominator ne zero
-- statement:
--   The Algebra construction uses the principal final denominator ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryParameters.lean#L37-L44
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryParameters.lean#L37-L44

import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.principal_final_denominator_ne_zero {t : ℝ} {d : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hd : ‖d‖ = 1) :
    (1 + d * (t : ℂ)) * (1 + (t : ℂ) / d) ≠ 0 := by sorry
