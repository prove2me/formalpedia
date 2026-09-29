-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag
-- name    : ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/eb3740e2-0f8a-56bd-a7fb-8908046f7310
-- title:
--   Diagonal modular polynomial has unit leading coefficient
-- statement:
--   Let $N$ be a natural number, nonzero, with $2 \le N$ and $N$ not a square in $\mathbb{N}$, and let `data` be a term of the structure [`ModularCurve.ModularPolynomialData N`](def/ModularCurve_X0.html#L215), that is: a polynomial $\Phi =$ `data.Φ` in $(\mathbb{Z}[X])[Y]$ which is monic, whose degree in $Y$ equals `dedekindPsi N` $= \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies the $q$-expansion relation `Φ.eval₂ evalAtJ (jqN N) = 0`, where `evalAtJ` is the ring homomorphism $\mathbb{Z}[X] \to$ `LaurentSeries ℚ` sending $X$ to `jq` and `jqN N` is the corresponding element attached to level $N$; so $\Phi$ is a modular polynomial of level $N$. The conclusion is that the diagonal specialisation $\Phi(X,X) \in \mathbb{Z}[X]$, formed as `data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X` (coefficients left alone, the outer variable sent to $X$), has leading coefficient a unit of $\mathbb{Z}$, i.e. equal to $\pm 1$. Nothing is asserted about the degree of $\Phi(X,X)$.
--
--   This is the classical statement that $\Phi_N(X,X)$ is, up to sign, monic when $N$ is not a perfect square, the source of integrality of singular moduli and of the $j$-invariants of curves carrying a cyclic endomorphism of degree $N$. It is used in the construction of integral models for isogeny endomorphism data, in [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j) and [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag
    (N : ℕ) [NeZero N] (h2 : 2 ≤ N) (hN : ¬ IsSquare N) (data : ModularCurve.ModularPolynomialData N) :
    IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff := by sorry
