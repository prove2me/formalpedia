-- Prove2me | Theorems.Thm_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed
-- name    : HopfAlgebra.faithfullyFlat_of_isReduced_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/33235dd4-9b45-5a96-aab9-6b3aec5f8a59
-- title:
--   Faithful flatness over a reduced Hopf subalgebra
-- statement:
--   Let $k$ be an algebraically closed field. Let $K$ be a commutative ring carrying a Hopf algebra structure over $k$ whose underlying $k$-algebra is of finite type, and assume $K$ is reduced. Let $H$ be a commutative ring carrying a Hopf algebra structure over $k$ whose underlying $k$-algebra is of finite type, and suppose $H$ is in addition a $K$-algebra in such a way that the $k$-, $K$- and $H$-actions form a scalar tower, so that the structure map $\mathrm{algebraMap}\colon K \to H$ is a $k$-algebra homomorphism. Assume that this map is compatible with the coalgebra structures over $k$ in the following two senses: for every $x \in K$, the comultiplication of the image of $x$ in $H$ equals the image of the comultiplication of $x$ under the map $K \otimes_k K \to H \otimes_k H$ induced on tensor products by $K \to H$ in each factor; and for every $x \in K$, the counit of the image of $x$ in $H$ equals the counit of $x$. Assume finally that $K \to H$ is injective. The conclusion is that $H$ is a faithfully flat $K$-module. No reducedness assumption is made on $H$.
--
--   This is the smooth (reduced) case of Takeuchi's theorem that a commutative Hopf algebra over a field is faithfully flat over any Hopf subalgebra: in geometric terms, a homomorphism of affine algebraic $k$-groups with dense image and reduced target is faithfully flat. Within the development it is used in the construction of reducedness statements for Cartier duals, namely by [`HopfAlgebra.isReduced_cartierDual_of_injective_of_surjective_of_ker_eq_map_zmodp`](thm.html#HopfAlgebra.isReduced_cartierDual_of_injective_of_surjective_of_ker_eq_map_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.faithfullyFlat_of_isReduced_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {K : Type v} [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K] [IsReduced K]
    {H : Type w} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H]
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K H) (IsScalarTower.toAlgHom k K H)
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    (hinj : Function.Injective (algebraMap K H)) :
    Module.FaithfullyFlat K H := by sorry
