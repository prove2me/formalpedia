-- Prove2me | Theorems.Thm_HopfAlgebra_FVect_hopfOrder_eq_of_le
-- name    : HopfAlgebra.FVect.hopfOrder_eq_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/308b7e40-9d4e-5edc-b7f7-eca8785a7f8b
-- title:
--   Uniqueness of Hopf orders of rank p^r F-vector space Hopf algebras
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, with fraction field $K$ (so $K$ is a field, an $R$-algebra, and the localisation of $R$ at its fraction field), let $p$ be a prime with $p \neq 2$ whose image in $R$ is irreducible, i.e. a uniformiser, and let $r \neq 0$. Let $F$ be a finite field with $\#F = p^r$, assume $p^r - 1$ is a unit of $R$, and fix a group homomorphism $\chi \colon F^\times \to R^\times$ together with a ring homomorphism $\iota \colon F \to R/\mathfrak{m}$ into the residue field such that the residue of $\chi(l)$ equals $\iota(l)$ for every $l \in F^\times$. Let $A$ be a commutative ring which is a Hopf algebra over $K$, an $R$-algebra compatibly with $R \to K$, cocommutative and finite as a $K$-module, with $\dim_K A = p^r$, and let $\sigma$ be an $F$-vector space structure on $A$: an assignment $a \mapsto \sigma.\mathrm{act}(a)$ of $K$-bialgebra endomorphisms of $A$ to elements of $F$ with $\sigma.\mathrm{act}(1) = \mathrm{id}$, $\sigma.\mathrm{act}(ab) = \sigma.\mathrm{act}(a) \circ \sigma.\mathrm{act}(b)$, $\sigma.\mathrm{act}(0)$ the unit of the convolution monoid on $K$-algebra endomorphisms of $A$, and $\sigma.\mathrm{act}(a+b)$ the convolution product of $\sigma.\mathrm{act}(a)$ and $\sigma.\mathrm{act}(b)$. Finally let $S, S'$ be $R$-subalgebras of $A$, each of which is module-finite over $R$, spans $A$ over $K$, has comultiplication landing in the range of the product map of the two inclusions $A \to A \otimes_K A$ restricted to the subalgebra (the image of $S \otimes_R S$, resp. $S' \otimes_R S'$), is stable under the antipode of $A$, and has counit values in the image of $R \to K$; that is, each is a Hopf order of $A$. Then $S \leq S'$ implies $S = S'$.
--
--   This is Raynaud's uniqueness of the finite flat prolongation of an $F$-vector space scheme of rank $q = p^r$ over a base of absolute ramification index $e = 1 < p-1$, in Hopf-algebra form: under these hypotheses $A$ has at most one Hopf order, so any two comparable Hopf orders coincide. It is used to obtain the corresponding uniqueness statement for Hopf orders admitting an $F$-vector space dévissage.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_FVect_hopfOrder_eq_of_le.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.FVect.hopfOrder_eq_of_le
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    (r : ℕ) [NeZero r]
    (F : Type w) [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
    (hq : IsUnit ((p ^ r : R) - 1))
    (χ : Fˣ →* Rˣ) (ι : F →+* IsLocalRing.ResidueField R)
    (hχ : ∀ l : Fˣ, IsLocalRing.residue R (χ l : R) = ι l)
    {A : Type v} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Coalgebra.IsCocomm K A] [Module.Finite K A] (hrank : Module.finrank K A = p ^ r)
    (σ : HopfAlgebra.FVectStructure F K A)
    (S S' : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hfin' : Module.Finite R ↥S') (hspan' : Submodule.span K (S' : Set A) = ⊤)
    (hcomul' : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range)
    (hanti' : ∀ x ∈ S', HopfAlgebra.antipode K (A := A) x ∈ S')
    (hcounit' : ∀ x ∈ S', Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hle : S ≤ S') : S = S' := by sorry
