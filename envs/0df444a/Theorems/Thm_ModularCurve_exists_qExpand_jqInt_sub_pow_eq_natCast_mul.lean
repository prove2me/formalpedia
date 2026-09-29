-- Prove2me | Theorems.Thm_ModularCurve_exists_qExpand_jqInt_sub_pow_eq_natCast_mul
-- name    : ModularCurve.exists_qExpand_jqInt_sub_pow_eq_natCast_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/9ad748e4-3238-57ac-9eca-64ae2492edb7
-- title:
--   Kronecker congruence for the integral j-expansion: j(q^q)≡ j(q)^q (mod q)
-- statement:
--   Let $q$ be a prime natural number. Work in the ring $\mathrm{LaurentSeries}\,\mathbb{Z}$ of Hahn series over $\mathbb{Z}$ with value group $\mathbb{Z}$, and let `jqInt` be the integral $j$-expansion, defined as the product of the Hahn series $\mathfrak q^{-1}$ (the single term of exponent $-1$ with coefficient $1$) with the Laurent series attached to the power series `jNum` $= E_4^3 \cdot \eta^{-}$, where `eisenstein4` is cubed and `dedekindEtaUnitInv` is the stated inverse unit. Let `qExpand ℤ q` be the ring endomorphism of $\mathrm{LaurentSeries}\,\mathbb{Z}$ obtained by transporting exponents along multiplication by $q$ on $\mathbb{Z}$, that is, the substitution $\mathfrak q \mapsto \mathfrak q^{q}$. The assertion is that there exists a Laurent series $h$ with integer coefficients such that $$\mathrm{qExpand}\,\mathbb{Z}\,q\,(\mathtt{jqInt}) - \mathtt{jqInt}^{\,q} = q\,h,$$ the scalar $q$ being the image of the natural number $q$ in $\mathrm{LaurentSeries}\,\mathbb{Z}$; equivalently, $j(\mathfrak q^{q}) - j(\mathfrak q)^{q}$ lies in the ideal $q\,\mathbb{Z}(\!(\mathfrak q)\!)$.
--
--   This is the $q$-expansion form of the Kronecker congruence, the coefficientwise Frobenius relation for the integral $j$-expansion, stated as an exact divisibility by $q$ inside $\mathbb{Z}(\!(\mathfrak q)\!)$ rather than as a congruence in characteristic $q$. It is used in the construction of the Deligne–Rapoport-style model data and in the level-structure arguments on $X_0$, in particular by [`ModularCurve.DRModelPackageLevel.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_comp_zero`](thm.html#ModularCurve.DRModelPackageLevel.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_comp_zero), [`ModularCurve.FullLevel.exists_qExpand_mem_gauss_xor_mem_comap_gauss_of_dvd_of_not_dvd_of_isLevelAutAt`](thm.html#ModularCurve.FullLevel.exists_qExpand_mem_gauss_xor_mem_comap_gauss_of_dvd_of_not_dvd_of_isLevelAutAt) and [`ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand`](thm.html#ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_qExpand_jqInt_sub_pow_eq_natCast_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_qExpand_jqInt_sub_pow_eq_natCast_mul (q : ℕ) [Fact q.Prime] :
    ∃ h : LaurentSeries ℤ, qExpand ℤ q jqInt - jqInt ^ q = (q : LaurentSeries ℤ) * h := by sorry
