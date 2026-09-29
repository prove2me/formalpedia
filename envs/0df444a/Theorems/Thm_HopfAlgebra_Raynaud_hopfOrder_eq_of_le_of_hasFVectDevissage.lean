-- Prove2me | Theorems.Thm_HopfAlgebra_Raynaud_hopfOrder_eq_of_le_of_hasFVectDevissage
-- name    : HopfAlgebra.Raynaud.hopfOrder_eq_of_le_of_hasFVectDevissage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/0524ff20-2027-56db-908b-f4c7d20aa621
-- title:
--   Nested Hopf orders of a dévissable Hopf algebra coincide
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain which is a discrete valuation ring) with fraction field $K$, let $p$ be a prime with $p \neq 2$, and assume the image of $p$ in $R$ is irreducible, i.e. $p$ is a uniformiser. Let $A$ be a commutative Hopf $K$-algebra which is cocommutative and finite-dimensional over $K$, equipped with an $R$-algebra structure making $R \to K \to A$ a scalar tower, and assume $A$ satisfies [`HopfAlgebra.HasFVectDevissage R K p A`](def/HopfAlgebra_HasFVectDevissage.html#L10): inductively, either $\dim_K A = 1$, or there is a surjective coalgebra-and-algebra map $\pi \colon A \to \bar A$ onto a finite cocommutative commutative Hopf $K$-algebra $\bar A$, an integer $r \geq 1$, a finite field $F$ with $\#F = p^{r}$ such that $p^{r} - 1$ is a unit of $R$, a character $\chi \colon F^{\times} \to R^{\times}$ and a ring map $\iota \colon F \to$ the residue field of $R$ with $\chi$ reducing to $\iota$, such that the Hopf kernel $\mathrm{hopfKer}\,\pi$ (the equaliser of the coaction of $\pi$ and $\mathrm{includeLeft} \colon A \to A \otimes_K \bar A$) has $K$-dimension $p^{r}$ and carries an `FVectStructure` over $F$ — an action of $F$ by algebra-coalgebra endomorphisms, multiplicative and unital for the multiplication of $F$ and additive for convolution, with $0$ acting as the convolution unit — while $\bar A$ again admits such a dévissage. Let $S, S' \subseteq A$ be $R$-subalgebras, each finite as an $R$-module, each spanning $A$ over $K$, each with comultiplication landing in the image of $S \otimes_R S \to A \otimes_K A$ (respectively $S' \otimes_R S'$), each stable under the antipode of $A$, and each with counit contained in the image of $R$ in $K$. If $S \leq S'$, then $S = S'$.
--
--   This is the rigidity statement underlying Raynaud's classification of group schemes of type $(p,\dots,p)$ over a base in which $p$ is a uniformiser: in absolute ramification $e = 1 < p-1$, a dévissable finite Hopf algebra admits no strictly nested pair of Hopf orders, so the Hopf order, when it exists, is unique. It is used in the proof of [`HopfAlgebra.bijective_baseChange_of_hasFVectDevissage`](thm.html#HopfAlgebra.bijective_baseChange_of_hasFVectDevissage).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_Raynaud_hopfOrder_eq_of_le_of_hasFVectDevissage.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_HasFVectDevissage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open scoped TensorProduct

theorem HopfAlgebra.Raynaud.hopfOrder_eq_of_le_of_hasFVectDevissage
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {A : Type v} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Coalgebra.IsCocomm K A] [Module.Finite K A]
    (hdev : HopfAlgebra.HasFVectDevissage R K p A)
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
