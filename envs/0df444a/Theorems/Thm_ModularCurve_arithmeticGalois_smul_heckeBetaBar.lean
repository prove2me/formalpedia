-- Prove2me | Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeBetaBar
-- name    : ModularCurve.arithmeticGalois_smul_heckeBetaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/c0d7f272-059e-532c-9c96-c5981a02b30b
-- title:
--   Arithmetic Galois action commutes with the β degeneracy embedding
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $N,\ell$ be natural numbers with $\ell\neq 0$, and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $L$. For a natural number $M$ write $F_M$ for `modularFunctionFieldFull M`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series `qExpand ℚ d jq` for the nonzero divisors $d$ of $M$, and $L\cdot F_M$ for `laurentBaseChange L F_M`, the subfield of $L((q))$ generated over $L$ by the images of $F_M$ under the coefficientwise map $\mathbb{Q}((q))\to L((q))$ induced by $\mathbb{Q}\to L$. Let $x\in L\cdot F_N$. The map `heckeBetaBar L N ℓ` is the $L$-algebra homomorphism $L\cdot F_N\to L\cdot F_{N\ell}$ given on underlying Laurent series by `qExpand L ℓ`, i.e. by rescaling all exponents by $\ell$ ($q\mapsto q^{\ell}$). The element `arithmeticGalois F₀ σ` of `SemilinearAut L (laurentBaseChange L F₀)` is the pair consisting of the ring automorphism of $L\cdot F_0$ applying $\sigma$ to each Laurent coefficient and of $\sigma$ itself on $L$, acting by the scalar action $\bullet$. The assertion is the equality, in $L\cdot F_{N\ell}$, of $\sigma$ applied coefficientwise to $\beta(x)$ with $\beta$ applied to $\sigma$-applied-coefficientwise $x$.
--
--   This is the statement that the second degeneracy embedding $\beta$ between base-changed modular function fields, substitution $q\mapsto q^{\ell}$, is defined over $\mathbb{Q}$ and hence commutes with the coefficientwise action of $\mathrm{Aut}(L/\mathbb{Q})$. It is the equivariance input for transporting the Hecke correspondence $\alpha_*\circ\beta^*$ and its divisor- and Picard-group avatars along arithmetic Galois automorphisms, and is used in the statements about Hecke transport, degeneracy composites and arithmetic Frobenius on semistable specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithmeticGalois_smul_heckeBetaBar.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.arithmeticGalois_smul_heckeBetaBar {L : Type*} [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero ℓ] (σ : L ≃ₐ[ℚ] L) (x : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N)) : ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull (N * ℓ)) σ • (ModularCurve.heckeBetaBar L N ℓ x) = ModularCurve.heckeBetaBar L N ℓ (ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull N) σ • x) := by sorry
