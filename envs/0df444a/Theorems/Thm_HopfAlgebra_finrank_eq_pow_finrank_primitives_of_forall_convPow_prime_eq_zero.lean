-- Prove2me | Theorems.Thm_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero
-- name    : HopfAlgebra.finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/01a3bcaf-92f5-5a59-9908-02e2009a6d37
-- title:
--   dim_k A = p^{dim_k P(A)} for Hopf algebras with trivial Verschiebung
-- statement:
--   Let $k$ be a field of characteristic $p$, where $p$ is a prime, and let $A$ be a commutative ring carrying a Hopf algebra structure over $k$ which is finite-dimensional as a $k$-module and whose comultiplication is cocommutative. Consider the $k$-linear dual $A \to_{k} k$ equipped, via `WithConv`, with the convolution product coming from the comultiplication of $A$. The hypothesis `hV` asks that every element $\beta$ of this convolution algebra whose underlying functional satisfies $\beta(1) = 0$ has vanishing $p$-th convolution power, $\beta^{p} = 0$. Write $\mathrm{primitives}\ k\ A$ for the $k$-submodule of $A$ defined as the kernel of the linear map $\Delta - (x \mapsto x \otimes 1) - (x \mapsto 1 \otimes x)$, that is, the space of $x \in A$ with $\Delta x = x \otimes 1 + 1 \otimes x$. The conclusion is the equality of natural numbers $$\dim_k A = p^{\,\dim_k \mathrm{primitives}\ k\ A}.$$
--
--   In the language of finite commutative group schemes $G = \operatorname{Spec} A$ over $k$, the hypothesis says that the Frobenius of the Cartier dual $G^{D}$ kills its augmentation ideal (equivalently, the Verschiebung of $G$ vanishes), and the conclusion computes the order of $G$ as $p$ to the dimension of $\operatorname{Hom}(G, \mathbb{G}_a)$, the space of primitive elements of $A$. It is used in the construction of the mod $p$ Dieudonné realisation, for the results on Dieudonné modules of group schemes with local Cartier dual and for the surjectivity statement on primitive elements; the proof invokes the corresponding count for bialgebras in terms of the cotangent space of the kernel of the counit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0) :
    Module.finrank k A = p ^ Module.finrank k ↥(primitives k A) := by sorry
