-- Prove2me | Theorems.Thm_HopfAlgebra_FVectStructure_exists_restrict_hopfOrder
-- name    : HopfAlgebra.FVectStructure.exists_restrict_hopfOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/5123f86e-d815-5d9f-933a-f77d04ea70ee
-- title:
--   Restricting an F-vector space structure to a Hopf order
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K$, let $A$ be a commutative ring which is a Hopf algebra over $K$ and an $R$-algebra compatibly with $R \to K$, let $F$ be a field, and let $\sigma$ be an $F$-vector space structure on $A$ over $K$: a family $a \mapsto \sigma.\mathrm{act}\,a$ of $K$-bialgebra endomorphisms of $A$, indexed by $a \in F$, with $\sigma.\mathrm{act}\,1 = \mathrm{id}$, $\sigma.\mathrm{act}(ab) = (\sigma.\mathrm{act}\,a)\circ(\sigma.\mathrm{act}\,b)$, $\sigma.\mathrm{act}\,0$ equal to the unit of the convolution monoid on $K$-algebra maps $A \to A$, and $\sigma.\mathrm{act}(a+b)$ equal to the convolution product of $\sigma.\mathrm{act}\,a$ and $\sigma.\mathrm{act}\,b$. Let $S \subseteq A$ be an $R$-subalgebra which is module-finite over $R$ (`hfin`), whose $K$-span is all of $A$ (`hspan`), such that $\Delta(x)$ lies in the image of the product map $S \otimes_R S \to A \otimes_K A$ for every $x \in S$ (`hcomul`), the antipode maps $S$ into $S$ (`hanti`), $\varepsilon(S)$ lies in the image of $R \to K$ (`hcounit`), and $\sigma.\mathrm{act}\,a$ maps $S$ into $S$ for every $a \in F^{\times}$ (`hstab`). Equipping $S$ with the descended $R$-bialgebra structure [`HopfOrder.bialgebraOfFinite`](def/HopfAlgebra_HopfOrderData.html#L1080) obtained from `hcomul` and `hcounit`, the conclusion asserts the existence of an $F$-vector space structure $\tau$ on the $R$-bialgebra $S$ with $\tau.\mathrm{act}\,a\,(s) = \sigma.\mathrm{act}\,a\,(s)$ in $A$ for all $a \in F$ and $s \in S$.
--
--   This is the step, in Raynaud's theory of group schemes of type $(p,\dots,p)$, that an $F^{\times}$-stable order in an $F$-vector space scheme over $K$ is itself an $F$-vector space scheme over $R$, isolated here as a restriction statement for the $F$-action alone. It is used by [`HopfAlgebra.FVect.hopfOrder_eq_of_le_of_forall_act_mem`](thm.html#HopfAlgebra.FVect.hopfOrder_eq_of_le_of_forall_act_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_FVectStructure_exists_restrict_hopfOrder.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.FVectStructure.exists_restrict_hopfOrder
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {F : Type*} [Field F] (σ : HopfAlgebra.FVectStructure F K A)
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hstab : ∀ (a : Fˣ), ∀ x ∈ S, σ.act (a : F) x ∈ S) :
    haveI : Module.Finite R ↥S := hfin
    letI : Bialgebra R ↥S := HopfOrder.bialgebraOfFinite (K := K) S hcomul hcounit
    ∃ τ : HopfAlgebra.FVectStructure F R ↥S, ∀ (a : F) (s : ↥S), ((τ.act a s : ↥S) : A) = σ.act a (s : A) := by sorry
