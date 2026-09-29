-- Prove2me | Theorems.Thm_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order
-- name    : ModularCurve.coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/ab4e4858-204b-5e2d-87fa-8e54fbac48a1
-- title:
--   Logarithmic q-derivative: no polar part, constant term the order
-- statement:
--   Let $k$ be a field and let $f$ be a nonzero element of the field of formal Laurent series `LaurentSeries k` (Hahn series over $k$ with integer exponents). Write $\theta$ for the $k$-linear operator `thetaL k` on `LaurentSeries k` defined by $\theta g = \mathfrak q \cdot g'$, that is, multiplication of the derivative of $g$ by the series `single 1 1` with single nonzero coefficient $1$ in degree $1$. The theorem asserts two things about the logarithmic $q$-derivative $H = f^{-1} \cdot \theta f$, formed using the inverse of $f$ in the Laurent series field: first, that the coefficient of $H$ in degree $n$ vanishes for every integer $n < 0$, so that $H$ has no polar part and is in fact a power series; and second, that the coefficient of $H$ in degree $0$ equals the image in $k$ of the order `f.order` of $f$ under the canonical ring homomorphism $\mathbb Z \to k$.
--
--   This is the algebraic form of the statement that the logarithmic differential $df/f$ attached to a nonzero Laurent series is regular with residue the order of $f$, read off from the $q$-expansion at the cusp. It is used in the study of the $q$-expansion of logarithmic differentials on modular curves, and is cited by [`ModularCurve.coeff_inv_mul_thetaL_mul_char_eq_pow`](thm.html#ModularCurve.coeff_inv_mul_thetaL_mul_char_eq_pow) and by [`ModularCurve.eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg`](thm.html#ModularCurve.eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order
    (k : Type*) [Field k] (f : LaurentSeries k) (hf : f ≠ 0) :
    (∀ n : ℤ, n < 0 → (f⁻¹ * thetaL k f).coeff n = 0) ∧
    (f⁻¹ * thetaL k f).coeff 0 = (f.order : k) := by sorry
