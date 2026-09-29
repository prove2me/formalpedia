-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime_of_not_dvd
-- name    : ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_prime_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/156726b8-ae94-5e07-bf30-fb3528e0a02c
-- title:
--   Separability of Φ̄_N over 𝔽̄_ℓ(X), prime level
-- statement:
--   Let $N$ be a prime and let `data` be a `ModularPolynomialData N`, that is: a polynomial $\Phi \in (\mathbb Z[X])[Y]$ which is monic in $Y$, whose degree in $Y$ equals `dedekindPsi N` $=\sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies $\Phi = 0$ after evaluating its coefficients by the ring homomorphism `evalAtJ` $\colon \mathbb Z[X] \to$ `LaurentSeries ℚ` sending $X$ to the $q$-expansion `jq` and substituting `jqN N` for $Y$. Let $\ell$ be a prime with $\ell \nmid N$, and write $k =$ `AlgebraicClosure (ZMod ℓ)`. The assertion is that the polynomial in $Y$ obtained from $\Phi$ by first reducing all its integer coefficients into $k$, coefficientwise via `Polynomial.mapRingHom (Int.castRingHom k)` (so landing in $(k[X])[Y]$), and then mapping the coefficients along the structure map $k[X] \to$ `RatFunc k`, is separable, i.e. coprime to its derivative as an element of `RatFunc k`$[Y]$. Nothing beyond separability is claimed: neither irreducibility nor the degree $[\,\cdot\,]$ statement over $k(X)$ is part of the conclusion.
--
--   This is the separability half of Igusa's theorem that, for $\ell \nmid N$, the degeneracy map $X_0(N) \to X(1)$ remains generically étale in characteristic $\ell$, here in the case of prime level $N$. It feeds the construction of good-reduction specialisations of the $j$-line and the Hecke descent data used in the fibrewise analysis of $X_0(N)$ in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_prime_of_not_dvd (N : ℕ) [Fact N.Prime] (data : ModularCurve.ModularPolynomialData N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure (ZMod ℓ))))).map
      (algebraMap (Polynomial (AlgebraicClosure (ZMod ℓ))) (RatFunc (AlgebraicClosure (ZMod ℓ))))).Separable := by sorry
