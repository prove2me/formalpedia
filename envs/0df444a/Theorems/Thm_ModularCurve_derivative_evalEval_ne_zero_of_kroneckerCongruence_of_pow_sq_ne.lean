-- Prove2me | Theorems.Thm_ModularCurve_derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne
-- name    : ModularCurve.derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/c5b9a584-31fa-576f-8a3c-dd33f0848066
-- title:
--   Nonvanishing derivatives of Φ_ℓ at (b,b^ℓ) in characteristic ℓ
-- statement:
--   Let $\ell$ be a prime and let `data` be modular polynomial data of level $\ell$: a bivariate polynomial $\Phi =$ `data.Φ` $\in \mathbb{Z}[X][Y]$ which is monic in the outer variable $Y$, of degree $\psi(\ell)=\sum_{d\mid\ell,\ d\ \text{squarefree}}\ell/d$ in $Y$, and which satisfies $\Phi(j(q), j(q^{\ell}))=0$ as an identity of Laurent series (the substitution of `evalAtJ` for the inner variable and of `jqN ℓ` for the outer one). Assume the Kronecker congruence `KroneckerCongruence ℓ data`: the coefficientwise reduction of $\Phi$ modulo $\ell$ equals $(C(X)^{\ell}-Y)\,(C(X)-Y^{\ell})$ in $(\mathbb{Z}/\ell)[X][Y]$, i.e. $\bar\Phi = (X^{\ell}-Y)(X-Y^{\ell})$. Let $k$ be a field of characteristic $\ell$ and $b\in k$ with $b^{\ell^{2}}\neq b$. Write $\bar\Phi_k$ for the image of $\Phi$ in $k[X][Y]$ under coefficientwise reduction, and let `derivative` be differentiation in the outer variable $Y$. Then both $\partial_Y\bar\Phi_k$ and $\partial_Y\overline{(\Phi^{T})}_k$, where $\Phi^{T}=$ `swapBivar Φ` interchanges the two variables, are nonzero when the inner variable is set to $b$ and the outer variable to $b^{\ell}$; equivalently $\partial_Y\bar\Phi_k(b,b^{\ell})\neq 0$ and $\partial_X\bar\Phi_k(b^{\ell},b)\neq 0$.
--
--   This is the étaleness, in characteristic $\ell$, of the level-$\ell$ modular equation at a point of the graph of Frobenius whose coordinate does not lie in $\mathbb{F}_{\ell^{2}}$: at $(b,b^\ell)$ the factor $X^\ell-Y$ of Kronecker's congruence vanishes while the other factor does not, and symmetrically at $(b^\ell,b)$. It is used in the construction of plane models and charts for the three-coordinate description of $X_0(N\ell)$, where prolongations of places are required to be unramified along the $\Phi_\ell$-link.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial ModularCurve

theorem ModularCurve.derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne
    (ℓ : ℕ) [Fact ℓ.Prime] (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (b : k) (hb : b ^ (ℓ ^ 2) ≠ b) :
    (Polynomial.derivative (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval b (b ^ ℓ) ≠ 0 ∧
    (Polynomial.derivative ((swapBivar data.Φ).map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval b (b ^ ℓ) ≠ 0 := by sorry
