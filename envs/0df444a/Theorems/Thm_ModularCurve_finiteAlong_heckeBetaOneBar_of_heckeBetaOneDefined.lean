-- Prove2me | Theorems.Thm_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined
-- name    : ModularCurve.finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/5df1a13e-b6e6-542c-8cf4-18fa71d22ac6
-- title:
--   Finiteness of the β₁ degeneracy extension at level Γ₁(N)
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $N$ and $\ell$ be nonzero natural numbers. Write $F(\Gamma_1(N)) =$ `x1FunctionFieldC ℚ N` for the subfield of $\mathbb{Q}$-Laurent series attached to $\Gamma_1(N)$, and $F(\Gamma_1(N)\cap\Gamma_0(N\ell)) =$ `x1x0FunctionFieldC ℚ N (N*ℓ)`, which by definition is the $q$-expansion field `qExpFunctionFieldC ℚ (Gamma1 N ⊓ Gamma0 (N*ℓ))`. Assume [`ModularCurve.HeckeBetaOneDefined N ℓ`](def/ModularCurve_X1HeckeOperator.html#L84), that is: for every $y \in F(\Gamma_1(N))$ the Laurent series `qExpand ℚ ℓ y`, obtained by the substitution $q \mapsto q^{\ell}$ (the ring endomorphism of Laurent series re-indexing exponents by multiplication by $\ell$), lies in $F(\Gamma_1(N)\cap\Gamma_0(N\ell))$. Then the $L$-algebra map `heckeBetaOneBar L N ℓ`, which under this hypothesis is the map induced by $q \mapsto q^{\ell}$ between the base changes to $L$ of these two fields — each base change being the subfield of $L$-Laurent series generated over $L$ by the image of the coefficient embedding $\mathbb{Q} \to L$ applied to the given field — satisfies [`AlgebraicCurve.FiniteAlong L`](def/AlgebraicCurve_Correspondence.html#L37): the target $L\cdot F(\Gamma_1(N)\cap\Gamma_0(N\ell))$ is a finite module over $L\cdot F(\Gamma_1(N))$ for the algebra structure transported along that map.
--
--   This is the finiteness of the second degeneracy extension of modular function fields, the one induced by $\tau \mapsto \ell\tau$ (equivalently $q \mapsto q^{\ell}$) from level $\Gamma_1(N)$ to level $\Gamma_1(N)\cap\Gamma_0(N\ell)$, valid for every $\ell \ge 1$ rather than only for primes. It underlies the treatment of the Hecke correspondence on $X_1(N)$, being used in the analysis of degeneracy pairs, of Hecke divisors and of the comparison of the Hecke action with the Abel–Jacobi map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined (L : Type*) [Field L]
    [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ]
    (h : ModularCurve.HeckeBetaOneDefined N ℓ) :
    AlgebraicCurve.FiniteAlong L (ModularCurve.heckeBetaOneBar L N ℓ) := by sorry
