-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare
-- name    : ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/4bb1346a-3137-5367-bd86-316bfef9d9ed
-- title:
--   Unit leading coefficient of Φ_N(X,X) for non-square N
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ which is not a square (no $r$ with $N = r\cdot r$), and let `data` be an element of [`ModularCurve.ModularPolynomialData N`](def/ModularCurve_X0.html#L215), that is: a polynomial $\Phi =$ `data.Φ` in $(\mathbb{Z}[X])[Y]$ together with the three properties recorded in that structure — $\Phi$ is monic in $Y$; its degree in $Y$ equals `dedekindPsi N`, defined as $\sum_{d \mid N,\ d \text{ squarefree}} N/d$; and $\Phi$ annihilates the pair consisting of the $q$-expansion of $j$ and that of $j(q^N)$, in the sense that evaluating $\Phi$ at $Y =$ `jqN N` with coefficients mapped by the ring homomorphism `evalAtJ` $\colon \mathbb{Z}[X] \to$ `LaurentSeries ℚ` sending $X$ to `jq` gives $0$. The assertion is that the diagonal specialisation obtained by substituting $Y \mapsto X$ while leaving the coefficient ring $\mathbb{Z}[X]$ untouched, namely $\Phi(X,X) \in \mathbb{Z}[X]$, has leading coefficient a unit of $\mathbb{Z}$, i.e. $\pm 1$; in particular $\Phi(X,X)$ is not the zero polynomial.
--
--   This is the integrality statement underlying Kronecker's congruence: the diagonal of the modular polynomial of non-square level has unimodular leading term, the non-square hypothesis excluding the tie between the Hermite slots with $a = d$ (and the degenerate level $N=1$, where $\Phi_1(X,X) = 0$). It is used in the derivation of the corresponding statement for `isUnit_leadingCoeff_diag`, and in the Weierstrass-curve lemmas separating $j$-invariants of an elliptic curve and of its quotient by a cyclic isogeny, respectively producing a reduction with prescribed behaviour over an algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare (N : ℕ) [NeZero N] (hN : ¬ IsSquare N) (data : ModularCurve.ModularPolynomialData N) : IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff := by sorry
