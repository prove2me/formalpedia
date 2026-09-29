-- Prove2me | Theorems.Thm_ModularCurve_modularPolynomialData_phi_unique_of_prime
-- name    : ModularCurve.modularPolynomialData_phi_unique_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/c1f8cd96-2e99-50fd-a581-07ef1eeeb9b4
-- title:
--   Uniqueness of the modular polynomial at prime level
-- statement:
--   Let $\ell$ be a natural number, nonzero and prime, and let `data` and `data'` be two terms of type [`ModularCurve.ModularPolynomialData ℓ`](def/ModularCurve_X0.html#L215). Such a term consists of a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ together with three conditions: $\Phi$ is monic (in $Y$); its $Y$-degree equals `dedekindPsi ℓ`, the sum of $\ell/d$ over the squarefree divisors $d$ of $\ell$ (which for prime $\ell$ is $\ell+1$); and $\Phi$ vanishes when its coefficients, which lie in $\mathbb{Z}[X]$, are mapped into the Laurent series field over $\mathbb{Q}$ by `evalAtJ`, the ring homomorphism substituting the $q$-expansion `jq` of $j$ for $X$, and $Y$ is evaluated at the $q$-expansion `jqN ℓ` of $j(q^{\ell})$; that is, $\Phi(j(q), j(q^{\ell})) = 0$. The conclusion is that the underlying polynomials coincide: `data.Φ = data'.Φ`. Thus the four data of such a structure pin down $\Phi$ uniquely, with no further normalisation required.
--
--   This is the uniqueness half of the classical statement that the modular polynomial $\Phi_\ell$ is the minimal polynomial of $j(q^{\ell})$ over $\mathbb{Q}(j)$, and it converts any existence statement about a modular-polynomial packet at prime level into a statement about every such packet. It is used in the derivation of the Kronecker congruence at prime level and in the construction of specialisations of places to level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularPolynomialData_phi_unique_of_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.modularPolynomialData_phi_unique_of_prime {ℓ : ℕ} [NeZero ℓ]
    (hℓ : ℓ.Prime) (data data' : ModularCurve.ModularPolynomialData ℓ) :
    data.Φ = data'.Φ := by sorry
