-- Prove2me | Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
-- name    : ModularCurve.exists_modularPolynomialData_evalSymm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/7c76ef27-0069-585b-bbdd-57d9873bc7ba
-- title:
--   Existence of a symmetric modular polynomial Φ_ℓ
-- statement:
--   Let $\ell$ be a prime. The theorem asserts the existence of a `ModularPolynomialData ℓ`, that is, of a polynomial $\Phi$ in one variable over $\mathbb{Z}[X]$ (an element of `Polynomial (Polynomial ℤ)`) such that: $\Phi$ is monic; its degree in the outer variable equals `dedekindPsi ℓ`, which for $N$ is defined as $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ and hence equals $\ell+1$ here; and $\Phi$ vanishes when its coefficients are mapped into the field `LaurentSeries ℚ` of formal Laurent series over $\mathbb{Q}$ by the ring homomorphism `evalAtJ`, the $\mathbb{Z}$-algebra map $\mathbb{Z}[X] \to \mathbb{Q}((q))$ sending $X$ to the $q$-expansion `jq`, and the outer variable is evaluated at the Laurent series `jqN ℓ` (the level-$\ell$ companion expansion). Moreover this $\Phi$ satisfies the predicate `EvalSymm`: for all Laurent series $x, y \in \mathbb{Q}((q))$, evaluating $\Phi$ by substituting $x$ into the coefficients (via `Polynomial.aeval`) and $y$ into the outer variable gives the same element of $\mathbb{Q}((q))$ as substituting $y$ into the coefficients and $x$ into the outer variable.
--
--   This is the existence of the classical modular polynomial $\Phi_\ell(X,Y)$ of prime level, monic of degree $\psi(\ell)=\ell+1$ in $Y$, with integral coefficients, annihilating the pair $(j(q), j(q^\ell))$ of $q$-expansions and symmetric in its two variables. It is the input from which the models of the modular curves $X_0(\ell)$ and their Hecke correspondences are built, and is cited throughout the treatment of fibres, cusp charts and places of those models; composite levels are handled separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularPolynomialData_evalSymm.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.exists_modularPolynomialData_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ := by sorry
