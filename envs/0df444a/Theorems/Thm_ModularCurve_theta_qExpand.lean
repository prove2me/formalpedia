-- Prove2me | Theorems.Thm_ModularCurve_theta_qExpand
-- name    : ModularCurve.theta_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/5b4d48aa-6df9-519d-ba46-a434d7471582
-- title:
--   θ = q d/dq against the substitution q ↦ q^N
-- statement:
--   Let $R$ be a commutative ring, let $N$ be a natural number that is nonzero, and let $f$ be a Laurent series over $R$, realised as a Hahn series over the ordered group $\mathbb{Z}$ with coefficients in $R$. Write $q =$ `HahnSeries.single (1 : ℤ) (1 : R)`, the Laurent series whose only nonzero coefficient is $1$ in degree $1$, and let $\theta$ denote the operator $g \mapsto q \cdot g'$, where $g'$ is `LaurentSeries.derivative`. Let `qExpand R N` be the ring homomorphism on Laurent series obtained by embedding the exponent domain along the additive map $k \mapsto Nk$ (injective and strictly monotone because $N \neq 0$); concretely it is the substitution $q \mapsto q^N$, sending the series with coefficients $a_k$ to the series whose coefficient in degree $Nk$ is $a_k$ and whose other coefficients vanish. The assertion is the identity
--   $$q \cdot \bigl(\mathrm{qExpand}_{R,N}(f)\bigr)' \;=\; N \cdot \mathrm{qExpand}_{R,N}\bigl(q \cdot f'\bigr)$$
--   in Laurent series over $R$, the right-hand side using the natural-number scalar action; that is, $\theta(f(q^N)) = N\,(\theta f)(q^N)$.
--
--   This is the elementary chain-rule compatibility of the differential operator $\theta = q\,d/dq$ with the degeneracy substitution $q \mapsto q^N$ on formal $q$-expansions. It is used in the $q$-expansion treatment of the modular curve $X_0(N)$, where expansions of the form $j(q^d)$ and their $\theta$-derivatives occur, and is cited by [`ModularCurve.coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq`](thm.html#ModularCurve.coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq) and [`ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D`](thm.html#ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_theta_qExpand.lean

import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.theta_qExpand {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : LaurentSeries R) : (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (qExpand R N f) = N • (qExpand R N ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f)) := by sorry
