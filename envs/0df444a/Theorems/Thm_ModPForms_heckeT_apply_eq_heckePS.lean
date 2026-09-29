-- Prove2me | Theorems.Thm_ModPForms_heckeT_apply_eq_heckePS
-- name    : ModPForms.heckeT_apply_eq_heckePS
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/cb7bd931-7f05-501e-98c1-1be3d70eccc5
-- title:
--   Agreement of the two normalisations of T_ℓ on power series
-- statement:
--   Let $F$ be a field, let $k$ be a natural number with $1 \le k$, let $\ell$ be a natural number and let $\varphi \in F[[X]]$ be a formal power series. The assertion is the equality of two power series obtained by applying two a priori differently normalised formal Hecke operators to $\varphi$. On the left, [`PowerSeries.heckeT ℓ k`](def/PowerSeries_FormalHeckeOperators.html#L33) is the $F$-linear endomorphism $U_\ell + (\ell)^{k-1}\cdot V_\ell$ of $F[[X]]$, where $U_\ell$ sends $f$ to the series whose $n$-th coefficient is the $(\ell n)$-th coefficient of $f$, $V_\ell$ sends $f$ to the series whose $n$-th coefficient is the $(n/\ell)$-th coefficient of $f$ when $\ell \mid n$ and $0$ otherwise, and the scalar $(\ell)^{k-1}$ is a power of the image of $\ell$ in $F$ with natural-number (truncated) exponent $k-1$. On the right, [`ModPForms.heckePS (k : ℤ) ℓ`](def/CuspForm_ModPForms.html#L20) is the coefficientwise operator whose $n$-th coefficient is the $(n\ell)$-th coefficient of $\varphi$ plus, when $\ell \mid n$, the product of $(\ell)^{k-1}$ in $F$ with integer exponent $(k : \mathbb{Z}) - 1$ and the $(n/\ell)$-th coefficient of $\varphi$, and $0$ otherwise. No primality or invertibility assumption on $\ell$ is made.
--
--   This identifies the operator $T_\ell = U_\ell + \ell^{k-1}V_\ell$ in its natural-number-exponent form with the coefficientwise description of $T_\ell$ in which the weight enters as an integer exponent; the hypothesis $1 \le k$ is exactly what makes the truncated subtraction $k - 1$ in $\mathbb{N}$ agree with $k - 1$ in $\mathbb{Z}$. It is used in the passage from mod $p$ eigenforms to the associated ring homomorphisms out of the Hecke algebra, in [`CuspForm.heckeAlgebra.exists_ringHom_apply_eq_of_isModPEigen_of_heckeU_eq_smul`](thm.html#CuspForm.heckeAlgebra.exists_ringHom_apply_eq_of_isModPEigen_of_heckeU_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_heckeT_apply_eq_heckePS.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.heckeT_apply_eq_heckePS (F : Type) [Field F] (k : ℕ) (hk : 1 ≤ k) (ℓ : ℕ) (φ : PowerSeries F) :
    PowerSeries.heckeT ℓ k φ = ModPForms.heckePS (k : ℤ) ℓ φ := by sorry
