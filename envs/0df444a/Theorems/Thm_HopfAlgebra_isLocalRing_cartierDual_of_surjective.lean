-- Prove2me | Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
-- name    : HopfAlgebra.isLocalRing_cartierDual_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/134692bd-e6f7-546a-a6bd-3ea117a3ce06
-- title:
--   Locality of the Cartier dual passes to bialgebra quotients
-- statement:
--   Let $k$ be a field, and let $A$ and $B$ be commutative rings carrying $k$-bialgebra structures whose comultiplications are cocommutative and which are finite as $k$-modules. Let $\pi : A \to B$ be a morphism of $k$-bialgebras (a map that is simultaneously an algebra and a coalgebra homomorphism over $k$), and assume $\pi$ is surjective. Here $\mathrm{CartierDual}\ k\ A$ denotes the $k$-linear dual $\operatorname{Hom}_k(A,k)$, equipped with the ring structure coming from the bialgebra structure of $A$ (convolution: multiplication dual to the comultiplication of $A$, unit the counit of $A$), and likewise for $B$. The hypothesis is that $\mathrm{CartierDual}\ k\ A$ is a local ring; the conclusion is that $\mathrm{CartierDual}\ k\ B$ is a local ring. In the language of group schemes: if $\operatorname{Spec} A$ is a finite commutative group scheme over $k$ whose Cartier dual has local coordinate ring, then the same holds for the closed subgroup scheme $\operatorname{Spec} B$ cut out by the surjection $\pi$.
--
--   This is the statement that unipotence (equivalently, connectedness of the Cartier dual) of a finite commutative group scheme over a field descends to quotients of its coordinate bialgebra, i.e. passes to closed subgroup schemes of the dual; it appears in Demazure–Gabriel IV §2. Within the formalisation it feeds the Dieudonné-module and deformation-theoretic material, being cited by results on Dieudonné data, $p$-divisible towers, and uniqueness of Hopf algebras with prescribed Dieudonné module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.isLocalRing_cartierDual_of_surjective
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (B : Type w) [CommRing B] [Bialgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π) (hA : IsLocalRing (CartierDual k A)) :
    IsLocalRing (CartierDual k B) := by sorry
