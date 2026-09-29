-- Prove2me | Theorems.Thm_ModularCurve_finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq
-- name    : ModularCurve.finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/7e1cc984-2a77-5f99-9976-12e56ebff098
-- title:
--   Relative degree of full modular function fields at a prime
-- statement:
--   For $N\ge 1$ write $F^{\mathrm{full}}_N$ for the project's field `modularFunctionFieldFull N`, the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}(\!(q)\!)$ (Laurent series over $\mathbb{Q}$) generated over $\mathbb{Q}$ by the set of Laurent series $\mathrm{qExpand}\,\mathbb{Q}\,d\;\mathrm{jq}$ for the nonzero divisors $d$ of $N$, i.e. by the $q$-expansions of $j$ rescaled by each divisor of $N$. Let $M$ be a nonzero natural number, $\ell$ a prime, and $M'$ a nonzero natural number with $M' = M\ell$. Let $\varphi \colon F^{\mathrm{full}}_{M} \to F^{\mathrm{full}}_{M'}$ be a ring homomorphism such that for every $f \in F^{\mathrm{full}}_{M}$ the underlying Laurent series of $\varphi(f)$ equals that of $f$; thus $\varphi$ is the inclusion read through the two subfield coercions. The assertion is that the rank of $F^{\mathrm{full}}_{M'}$ as a module over $F^{\mathrm{full}}_{M}$, for the module structure coming from the algebra structure induced by $\varphi$, is finite and equal to $\ell$ if $\ell \mid M$, and to $\ell+1$ otherwise. The larger level appears as a separate variable $M'$ constrained by $M' = M\ell$, so that consumers whose level is written in another order can instantiate the result directly.
--
--   This is the classical statement that the degree of the level-$M\ell$ full modular function field over the level-$M$ one equals $\psi(M\ell)/\psi(M) = [\Gamma_0(M):\Gamma_0(M\ell)]$, namely $\ell$ when $\ell \mid M$ and $\ell+1$ otherwise. It is used in the project to compute ranks attached to degeneracy maps between modular curves of level $M$ and $M\ell$, for instance by [`ModularCurve.DRModelPackageLevel.finrank_pi_eq`](thm.html#ModularCurve.DRModelPackageLevel.finrank_pi_eq) and by the existence results for pinned degeneracy pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq
    (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime] (M' : ℕ) [NeZero M'] (hM' : M' = M * ℓ)
    (φ : ↥(modularFunctionFieldFull M) →+* ↥(modularFunctionFieldFull M'))
    (hφ : ∀ f : ↥(modularFunctionFieldFull M),
      ((φ f : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) = ((f : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) :
    @Module.finrank ↥(modularFunctionFieldFull M) ↥(modularFunctionFieldFull M') _ _ φ.toAlgebra.toModule =
      (if ℓ ∣ M then ℓ else ℓ + 1) := by sorry
