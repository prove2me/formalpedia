-- Prove2me | Theorems.Thm_ModularCurve_heckeGen_smul_galois_smul
-- name    : ModularCurve.heckeGen_smul_galois_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/99e39580-6d58-5905-a7a9-0ef1aca4fb0b
-- title:
--   Hecke action on J₀(N)_{ℚ̄} is Galois-equivariant
-- statement:
--   Let $N$ be a nonzero natural number, let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $\ell$ be a prime, and let $y$ be an element of `JZero N`, that is, of the degree-zero divisor class group `Pic0` of the field `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ — the base change to $\overline{\mathbb{Q}}$, inside the Laurent series field $\overline{\mathbb{Q}}((t))$, of the full modular function field of level $N$ — so $y$ is a class of a degree-zero divisor modulo the subgroup of principal divisors. The group `JZero N` carries the `DistribMulAction` of $\overline{\mathbb{Q}}$-automorphisms coming from the arithmetic Galois action, and the module structure `heckeModuleBar N` over the Hecke algebra `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ (a polynomial ring in one variable per prime), defined by sending $X_\ell$ to `heckeOperatorBar N ℓ` whenever the predicate `HeckeOperatorsCommuteBar N` holds, i.e. whenever these operators commute pairwise, and to $0$ otherwise. With respect to this module structure, the assertion is that the generator `heckeGen ℓ` $= X_\ell$ satisfies $X_\ell \cdot (\sigma \cdot y) = \sigma \cdot (X_\ell \cdot y)$.
--
--   This is the $\mathbb{Q}$-rationality of the Hecke correspondences on $X_0(N)$, in the form of Galois equivariance of the Hecke action on the modular Jacobian; it is what makes Hecke torsion subgroups of $J_0(N)$ into Galois modules. It is used in the construction and analysis of the Galois representations attached to eigenforms and in the study of the reduction of $J_0(N)$ at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeGen_smul_galois_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.heckeGen_smul_galois_smul (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ℓ : Nat.Primes) (y : JZero N) :
    (letI := heckeModuleBar N;
      heckeGen ℓ • (σ • y) = σ • (heckeGen ℓ • y)) := by sorry
