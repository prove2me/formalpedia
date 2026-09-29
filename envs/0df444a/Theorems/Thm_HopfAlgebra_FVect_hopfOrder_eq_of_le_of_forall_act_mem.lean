-- Prove2me | Theorems.Thm_HopfAlgebra_FVect_hopfOrder_eq_of_le_of_forall_act_mem
-- name    : HopfAlgebra.FVect.hopfOrder_eq_of_le_of_forall_act_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/f777efa5-c58f-523c-af34-c199430b71d0
-- title:
--   Rigidity of F^×-stable Hopf orders when p is a uniformiser
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (the fraction-field hypothesis being that $K$ is a field with an $R$-algebra structure making it a fraction ring of $R$), let $p$ be a prime with $p \neq 2$ such that the image of $p$ in $R$ is irreducible, and let $r \neq 0$. Let $F$ be a finite field with $\#F = p^r$, assume $p^r - 1$ is a unit of $R$, and let $\chi \colon F^\times \to R^\times$ be a group homomorphism and $\iota \colon F \to R/\mathfrak m$ a ring homomorphism to the residue field with $\chi(l) \bmod \mathfrak m = \iota(l)$ for all $l \in F^\times$. Let $A$ be a commutative cocommutative Hopf algebra over $K$, finite over $K$ with $\dim_K A = p^r$, carrying an $R$-algebra structure compatible with that of $K$, and let $\sigma$ be an $F$-vector space structure on $A$ over $K$ in Raynaud's sense: a map $a \mapsto \sigma.\mathrm{act}\,a$ from $F$ to the $K$-bialgebra endomorphisms of $A$ with $\sigma.\mathrm{act}\,1 = \mathrm{id}$, $\sigma.\mathrm{act}(ab) = (\sigma.\mathrm{act}\,a)\circ(\sigma.\mathrm{act}\,b)$, $\sigma.\mathrm{act}\,0$ the unit of the convolution monoid of $K$-algebra endomorphisms of $A$, and $\sigma.\mathrm{act}(a+b)$ the convolution product of $\sigma.\mathrm{act}\,a$ and $\sigma.\mathrm{act}\,b$. Let $S \subseteq S'$ be $R$-subalgebras of $A$, each of which is module-finite over $R$, spans $A$ as a $K$-module, has $\Delta(x)$ in the image of the $R$-algebra map $S \otimes_R S \to A \otimes_K A$ induced by the two inclusions for every $x$ in it, is stable under the antipode of $A$, and has counit values in the image of $R \to K$; assume finally that each of $S$ and $S'$ is stable under $\sigma.\mathrm{act}\,a$ for every $a \in F^\times$. Then $S = S'$.
--
--   This is Raynaud's rigidity statement for $F$-vector space group schemes in absolute ramification $e = 1$: over a discrete valuation ring in which an odd prime $p$ is a uniformiser, an $F^\times$-stable Hopf order of a cocommutative Hopf algebra of dimension $\#F$ with an $F$-vector space structure is unique among those containing it. It is used to derive the unconditional uniqueness statement [`HopfAlgebra.FVect.hopfOrder_eq_of_le`](thm.html#HopfAlgebra.FVect.hopfOrder_eq_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_FVect_hopfOrder_eq_of_le_of_forall_act_mem.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.FVect.hopfOrder_eq_of_le_of_forall_act_mem
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
    (hle : S ≤ S')
    (hS : ∀ (a : Fˣ), ∀ x ∈ S, σ.act (a : F) x ∈ S)
    (hS' : ∀ (a : Fˣ), ∀ x ∈ S', σ.act (a : F) x ∈ S') : S = S' := by sorry
