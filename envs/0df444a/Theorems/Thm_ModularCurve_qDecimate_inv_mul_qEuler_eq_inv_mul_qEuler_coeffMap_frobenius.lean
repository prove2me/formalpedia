-- Prove2me | Theorems.Thm_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius
-- name    : ModularCurve.qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/309984e4-6c6c-526b-a6e9-277dad3bdca1
-- title:
--   Decimation of a logarithmic vartheta-derivative commutes with Frobenius
-- statement:
--   Let $K$ be a field, let $p$ be a prime, and assume $K$ has characteristic $p$. Three operations on the Laurent series field $\mathrm{LaurentSeries}\ K = K((q))$ are involved. First, [`ModularCurve.qEuler`](def/ModularCurve_HeckeDifferential.html#L40) is the derivation $\vartheta$ sending $x$ to the series whose $n$-th coefficient is $n\cdot x_n$ (the coefficient index running over $\mathbf{Z}$, with $n$ mapped into $K$), i.e. $\vartheta = q\,d/dq$. Second, [`ModularCurve.qDecimate K p`](def/ModularCurve_XHDifferentialsModL.html#L74) is the $K$-linear map sending $x$ to the series whose $k$-th coefficient is $x_{pk}$. Third, [`ModularCurve.coeffMap (frobenius K p)`](def/ModularCurve_LaurentCoeff.html#L16) is the ring homomorphism of $K((q))$ applying the $p$-power Frobenius of $K$ to each coefficient, $\sum a_n q^n \mapsto \sum a_n^{\,p} q^n$; write it as $\sigma$. The assertion is that for every $f \in K((q))$,
--   $$\mathrm{qDecimate}_p\bigl(f^{-1}\,\vartheta f\bigr) \;=\; (\sigma f)^{-1}\,\vartheta(\sigma f),$$
--   the inverses being taken in the field $K((q))$, so that both sides vanish when $f = 0$. Equivalently, writing $f^{-1}\vartheta f = \sum_n b_n q^n$, one has $b_{pn} = b_n^{\,p}$ for all $n \in \mathbf{Z}$.
--
--   This is the $q$-expansion form of Cartier's identity $C(df/f) = df/f$ for logarithmic differentials in characteristic $p$, stated purely as an identity in $K((q))$ for an arbitrary field of characteristic $p$ (no perfectness and no curve enter). It is used in the analysis of differentials mod $\ell$ on modular curves, where it feeds the identification of Frobenius-fixed logarithmic derivatives in [`ModularCurve.genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius`](thm.html#ModularCurve.genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : LaurentSeries K) :
    (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      ModularCurve.qDecimate K p (f⁻¹ * ModularCurve.qEuler K f)) =
      (ModularCurve.coeffMap (frobenius K p) f)⁻¹ *
        ModularCurve.qEuler K (ModularCurve.coeffMap (frobenius K p) f) := by sorry
