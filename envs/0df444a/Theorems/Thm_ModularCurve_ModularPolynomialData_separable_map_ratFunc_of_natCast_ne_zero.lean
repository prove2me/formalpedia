-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
-- name    : ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/8c3190db-8753-5cf7-8279-c48d70ab1a6d
-- title:
--   Separability of Φ_N over K(X) when N≠ 0 in K
-- statement:
--   Let $K$ be a field and $N$ a non-zero natural number, and let `data` be a modular polynomial packet of level $N$: a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, whose degree in $Y$ equals $\mathrm{dedekindPsi}(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies $\Phi(j(q), j(q^{N})) = 0$ in the field of rational Laurent series over $\mathbb{Q}$, the vanishing being expressed by evaluating the coefficients of $\Phi$ through the ring homomorphism `evalAtJ` (substitution of the $q$-expansion `jq` of $j$ into a polynomial over $\mathbb{Z}$) and the outer variable at `jqN N`, the expansion of $j$ in $q^{N}$. Assume that the image of $N$ in $K$ is non-zero. Then the polynomial obtained from $\Phi$ by reducing all integer coefficients modulo the characteristic, i.e. by applying `Polynomial.mapRingHom (Int.castRingHom K)` to its coefficients, and then passing from $K[X]$ to the rational function field $K(X)$ along the structure map, is separable as an element of $K(X)[Y]$, that is, it is coprime to its derivative.
--
--   This is the separability half of Igusa's theorem on Kroneckerian models at arbitrary level: the covering of the $j$-line defined by $\Phi_N$ is generically étale over any field in which $N$ is invertible. It underlies the construction of models of $X_0(N)$ in characteristic $p \nmid N$, and is invoked by the statements producing fibre models and place specialisations at such primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hNK : (N : K) ≠ 0) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable := by sorry
