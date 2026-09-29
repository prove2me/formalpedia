-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField
-- name    : HopfAlgebra.exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/9e7c647b-f726-5c34-84dc-41c944f070c9
-- title:
--   Galois-stable subgroups of points cut out by Hopf quotients
-- statement:
--   Let $K$ be a perfect field, $\bar K$ its algebraic closure, and let $A$ be a commutative Hopf algebra over $K$ that is finite-dimensional and cocommutative, and write $V = \mathrm{Hom}_{K\text{-alg}}(A,\bar K)$, viewed as a monoid under convolution (`WithConv`), assumed finite. Assume the evaluation map is bijective: the $\bar K$-algebra homomorphism $\bar K \otimes_K A \to (V \to \bar K)$ determined by the structure map of $\bar K$ and by $a \mapsto (\nu \mapsto \nu(a))$ is a bijection. Let $W \subseteq V$ be a submonoid for the convolution product which is Galois-stable in the following sense: for every $K$-algebra automorphism $\sigma$ of $\bar K$, every $\nu \in W$ and every $\nu' \in V$ with $\nu'(a) = \sigma(\nu(a))$ for all $a \in A$, one has $\nu' \in W$. Then there exist a commutative Hopf algebra $\bar A$ over $K$, cocommutative and finite-dimensional, and a surjective bialgebra homomorphism $\pi \colon A \to \bar A$ such that: every $K$-algebra map $\psi \colon \bar A \to \bar K$ satisfies $\psi \circ \pi \in W$; every $\nu \in W$ equals $\psi \circ \pi$ for some such $\psi$; $\dim_K \bar A = |W|$; every $K$-algebra map $h$ from the Hopf kernel $\mathrm{hopfKer}\,\pi$ — the subalgebra of $a \in A$ with $(\mathrm{id} \otimes \pi)(\Delta a) = a \otimes 1$ in $A \otimes_K \bar A$ — to $\bar K$ is the restriction of some $\nu \in V$ along the inclusion; two points $\nu, \nu' \in V$ have equal restrictions to $\mathrm{hopfKer}\,\pi$ if and only if $\nu' = \nu \cdot w$ for some $w \in W$; and $\dim_K(\mathrm{hopfKer}\,\pi) \cdot |W| = \dim_K A$.
--
--   This is the quotient half of the dictionary between finite étale commutative group schemes over $K$ and finite Galois modules: a Galois-stable subgroup $W$ of $V = G(\bar K)$ is the group of $\bar K$-points of a closed subgroup scheme $\operatorname{Spec} \bar A \subseteq \operatorname{Spec} A$ defined over $K$, and the quotient $\operatorname{Spec}(\mathrm{hopfKer}\,\pi)$ has point set $V/W$. It feeds the dévissage of such Hopf algebras along a composition series of the corresponding Galois module, used in [`HopfAlgebra.hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField`](thm.html#HopfAlgebra.hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField
    (K : Type u) [Field K] [PerfectField K]
    (A : Type v) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Finite (WithConv (A →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (W : Submonoid (WithConv (A →ₐ[K] AlgebraicClosure K)))
    (hW : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ ν ∈ W,
      ∀ ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) → ν' ∈ W) :
    ∃ (Ā : Type v) (_ : CommRing Ā) (_ : HopfAlgebra K Ā) (_ : Coalgebra.IsCocomm K Ā) (_ : Module.Finite K Ā)
      (π : A →ₐc[K] Ā), Function.Surjective π ∧
      (∀ ψ : Ā →ₐ[K] AlgebraicClosure K, WithConv.toConv (ψ.comp (π : A →ₐ[K] Ā)) ∈ W) ∧
      (∀ ν ∈ W, ∃ ψ : Ā →ₐ[K] AlgebraicClosure K, ψ.comp (π : A →ₐ[K] Ā) = WithConv.ofConv ν) ∧
      Module.finrank K Ā = Nat.card ↥W ∧
      (∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
        ∃ ν : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h) ∧
      (∀ ν ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃ w ∈ W, ν' = ν * w) ∧
      Module.finrank K ↥(HopfAlgebra.hopfKer π) * Nat.card ↥W = Module.finrank K A := by sorry
