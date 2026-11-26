-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_coe_pow_norm_lt_one
-- name    : FourierJacobi.Algebra.coe_pow_norm_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:42.992777+00:00
-- url     : https://prove2.me/theorems/0ca2b71a-ab95-4c5d-8d5b-8fb07a10a26f
-- title:
--   Algebra: coe pow norm lt one
-- statement:
--   The Algebra construction uses the coe pow norm lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L28-L31
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L28-L31

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem FourierJacobi.Algebra.coe_pow_norm_lt_one {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {n : ℕ} (hn : n ≠ 0) : ‖(t : ℂ) ^ n‖ < 1 := by sorry
