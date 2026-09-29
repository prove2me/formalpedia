-- Prove2me | Theorems.Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_wittHomShift_surjective
-- name    : HopfAlgebra.wittHomMap_surjective_of_surjective_of_wittHomShift_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/61b6f164-429d-5285-8408-0c879999a309
-- title:
--   Surjectivity of Hom(-,Wₙ) at a saturating level
-- statement:
--   Let $k$ be a perfect field of characteristic $p$ for a prime $p$, let $n$ be a nonzero natural number, let $A$ be a commutative ring which is a Hopf algebra over $k$, finite-dimensional as a $k$-module and with cocommutative comultiplication, and let $B$ be a commutative ring which is a $k$-bialgebra. Let $\pi : A \to B$ be a $k$-bialgebra homomorphism which is surjective as a function. For a $k$-bialgebra $C$, [`Deformation.wittHom k p n C`](def/Dieudonne_WittVectorHom.html#L246) denotes the additive subgroup of the truncated Witt vectors $W_n(C)$ consisting of those $x$ with $W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x)$ in $W_n(C \otimes_k C)$, where $\Delta$ is the comultiplication and $\iota_1, \iota_2$ are the two inclusions of $C$ into $C \otimes_k C$; [`Deformation.wittHomShift k p n A`](def/Dieudonne_WittVectorHom.html#L446) is the additive map from this subgroup at level $n$ to the one at level $n+1$ induced by the map $W_n(A) \to W_{n+1}(A)$ obtained from the Verschiebung through truncation, and [`Deformation.wittHomMap p n \pi`](def/Dieudonne_WittVectorHom.html#L339) is the additive map between these subgroups induced by applying $W_n$ to $\pi$. Assume [`Deformation.wittHomShift k p n A`](def/Dieudonne_WittVectorHom.html#L446) is surjective. Then [`Deformation.wittHomMap p n π`](def/Dieudonne_WittVectorHom.html#L339) is surjective.
--
--   In scheme-theoretic language, with $G = \operatorname{Spec} A$ a finite commutative group scheme over $k$ and $H = \operatorname{Spec} B$ a closed subgroup scheme, this is the right exactness at finite level of $\operatorname{Hom}(-, W_n)$: every homomorphism $H \to W_n$ extends to $G$, under the hypothesis that every homomorphism $G \to W_{n+1}$ factors through the Verschiebung $W_n \hookrightarrow W_{n+1}$. It is used to prove surjectivity of the map of Dieudonné modules associated with a surjection of bialgebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_wittHomShift_surjective.lean

import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem HopfAlgebra.wittHomMap_surjective_of_surjective_of_wittHomShift_surjective
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [NeZero n]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (B : Type w) [CommRing B] [Bialgebra k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π)
    (hsat : Function.Surjective (Deformation.wittHomShift k p n A)) :
    Function.Surjective (Deformation.wittHomMap p n π) := by sorry
