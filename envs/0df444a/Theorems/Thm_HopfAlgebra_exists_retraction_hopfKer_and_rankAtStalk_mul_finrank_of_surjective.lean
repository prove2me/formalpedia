-- Prove2me | Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
-- name    : HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/25408dd3-5552-50a2-b7ee-8ae93260e7af
-- title:
--   Hopf kernel of a surjection: retraction, projectivity and rank
-- statement:
--   Let $R$ be a commutative ring and let $A$ and $B$ be commutative Hopf $R$-algebras, each finite and free as an $R$-module. Let $\pi : A \to B$ be a morphism of Hopf $R$-algebras (a bialgebra map, `A →ₐc[R] B`) which is surjective as a function. Write $A^{\mathrm{co}\,\pi} =$ [`HopfAlgebra.hopfKer π`](def/HopfAlgebra_HopfKer.html#L19) for the $R$-subalgebra of $A$ on which the composite of the comultiplication $A \to A \otimes_R A$ with $\mathrm{id}_A \otimes \pi$ agrees with $a \mapsto a \otimes 1$, i.e. the equalizer of these two $R$-algebra maps $A \to A \otimes_R B$. The assertion is a conjunction of four statements: (i) there exists an $A^{\mathrm{co}\,\pi}$-linear map $r : A \to A^{\mathrm{co}\,\pi}$ with $r(c) = c$ for every $c \in A^{\mathrm{co}\,\pi}$, so that $A^{\mathrm{co}\,\pi}$ is a direct summand of $A$ over itself; (ii) $A^{\mathrm{co}\,\pi}$ is a finitely generated $R$-module; (iii) $A^{\mathrm{co}\,\pi}$ is a projective $R$-module; and (iv) for every prime $\mathfrak{p}$ of $R$, the rank of $A^{\mathrm{co}\,\pi}$ at the stalk at $\mathfrak{p}$, multiplied by $\operatorname{rank}_R B$, equals $\operatorname{rank}_R A$.
--
--   In geometric terms this is the structure theorem for the quotient of a finite locally free commutative group scheme $G = \operatorname{Spec} A$ by a finite locally free closed subgroup $H = \operatorname{Spec} B$: the coordinate ring of $G/H$ is a finite projective $R$-module, a direct summand of $A$, and orders multiply, $|G| = |H| \cdot |G/H|$. It is obtained from the $H$-torsor property of $A$ over $A^{\mathrm{co}\,\pi}$ ([`HopfAlgebra.isHopfGalois_of_surjective`](thm.html#HopfAlgebra.isHopfGalois_of_surjective)) together with finiteness and projectivity of $A$ over the Hopf kernel ([`HopfAlgebra.finite_projective_hopfKer_of_surjective`](thm.html#HopfAlgebra.finite_projective_hopfKer_of_surjective)), and it feeds the order and rank computations for Cartier duals and Dieudonné modules used in the deformation-theoretic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    (∃ r : A →ₗ[↥(HopfAlgebra.hopfKer π)] ↥(HopfAlgebra.hopfKer π),
        ∀ c : ↥(HopfAlgebra.hopfKer π), r (c : A) = c) ∧
      Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Projective R ↥(HopfAlgebra.hopfKer π) ∧
      ∀ 𝔭 : PrimeSpectrum R,
        Module.rankAtStalk (R := R) ↥(HopfAlgebra.hopfKer π) 𝔭 * Module.finrank R B =
          Module.finrank R A := by sorry
