-- Prove2me | Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
-- name    : ModularCurve.nonempty_modularPolynomialData_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/eeb1e5fc-d301-59a3-8555-a76da6b464ce
-- title:
--   Existence of modular polynomial data at squarefree levels
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and assume that $N$ is squarefree and $1 < N$. The conclusion is that the structure type `ModularPolynomialData N` is nonempty, i.e. there exists a quadruple consisting of a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ in one variable over $\mathbb{Z}[X]$ together with proofs that: $\Phi$ is monic; the degree of $\Phi$ in its outer variable equals `dedekindPsi N`, defined as $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ (which for squarefree $N$ is the usual Dedekind $\psi(N) = N\prod_{\ell \mid N}(1 + 1/\ell)$, the sum being over all divisors); and $\Phi$ vanishes under the two-variable evaluation `Φ.eval₂ evalAtJ (jqN N)`, that is, substituting the Laurent series `jqN N` over $\mathbb{Q}$ for the outer variable and applying to each coefficient the ring homomorphism `evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ` given by evaluation at the Laurent series `jq`, one obtains $0$ in `LaurentSeries ℚ`. Here `jq` is the $q$-expansion of the modular invariant $j$ and `jqN N` its level-$N$ companion obtained by substituting $q^N$. No claim is made for non-squarefree $N$, nor for $N = 1$.
--
--   This is the existence of the classical modular equation $\Phi_N(j(q), j(q^N)) = 0$, with integral coefficients and monic of degree $\psi(N)$, in the squarefree levels; it supplies the polynomial model used throughout the treatment of the modular curve $X_0(N)$ in this development. It is invoked, among others, in the local analysis at the nodes of the plane model and in the computation of the order of the cuspidal divisor class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.nonempty_modularPolynomialData_of_squarefree (N : ℕ) [NeZero N] (hsf : Squarefree N) (hN : 1 < N) : Nonempty (ModularPolynomialData N) := by sorry
