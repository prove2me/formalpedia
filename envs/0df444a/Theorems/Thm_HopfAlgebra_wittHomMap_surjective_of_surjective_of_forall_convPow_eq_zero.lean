-- Prove2me | Theorems.Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
-- name    : HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/45cfb8e5-31ce-5cfe-b137-3cc751ed725e
-- title:
--   Restriction of length-n Witt homomorphisms is surjective
-- statement:
--   Let $k$ be a perfect field of characteristic $p$ for a prime $p$, let $n$ be a positive integer, let $A$ be a commutative ring carrying a Hopf algebra structure over $k$ which is finite-dimensional as a $k$-module and whose comultiplication is cocommutative, and let $B$ be a commutative ring carrying a bialgebra structure over $k$. Let $\pi : A \to B$ be a homomorphism of $k$-bialgebras which is surjective as a map of sets, and assume that in the convolution algebra structure on $\operatorname{Hom}_k(A,k)$ (the multiplication recorded by `WithConv`) every functional $\beta$ with $\beta(1) = 0$ satisfies $\beta^{p^n} = 0$, the power being taken for convolution. Consider, for a $k$-bialgebra $C$, the additive subgroup $\mathrm{wittHom}$ of the truncated Witt vectors $\mathbb{W}_n(C)$ consisting of those $x$ whose image under the functorial map induced by the comultiplication $C \to C \otimes_k C$ equals the sum of its images under the two maps induced by the inclusions $c \mapsto c \otimes 1$ and $c \mapsto 1 \otimes c$; equivalently, the group of homomorphisms $\operatorname{Spec} C \to W_n$. The conclusion is that the additive map $\mathrm{wittHom}(A) \to \mathrm{wittHom}(B)$ given by applying $\pi$ to the Witt coordinates, namely [`Deformation.wittHomMap p n π`](def/Dieudonne_WittVectorHom.html#L339), is surjective.
--
--   In geometric terms, with $G = \operatorname{Spec} A$ a finite commutative group scheme over $k$ whose Cartier dual has augmentation ideal killed by the $n$-th Frobenius power (equivalently $V_G^n = 0$) and $H = \operatorname{Spec} B \hookrightarrow G$ the closed subgroup cut out by $\pi$, the statement says that every homomorphism $H \to W_n$ extends to $G$, i.e. that the length-$n$ Witt group is injective in this category; it is the finite-level right exactness of the Dieudonné functor. It is used in the construction and comparison of Dieudonné modules, for instance in the results on local-ring Cartier duals and on the Fontaine–Hodge filtration that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [NeZero n]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (B : Type w) [CommRing B] [Bialgebra k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π)
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0) :
    Function.Surjective (Deformation.wittHomMap p n π) := by sorry
