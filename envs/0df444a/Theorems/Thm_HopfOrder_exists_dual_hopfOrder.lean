-- Prove2me | Theorems.Thm_HopfOrder_exists_dual_hopfOrder
-- name    : HopfOrder.exists_dual_hopfOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/51e3ace4-1629-509b-86b0-f07d177467f5
-- title:
--   Dual of a Hopf order is a Hopf order of the Cartier dual
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K$, and let $A$ be a commutative $K$-algebra carrying a Hopf algebra structure over $K$ which is finite-dimensional as a $K$-module and whose comultiplication is cocommutative; $A$ is also an $R$-algebra compatibly with its $K$-structure, and the Cartier dual [`CartierDual K A`](def/HopfAlgebra_CartierDual.html#L12), which by definition is the $K$-linear dual $\operatorname{Hom}_K(A,K)$ equipped with its Hopf algebra structure, is likewise given a compatible $R$-algebra structure. Let $S$ be an $R$-subalgebra of $A$ such that: $S$ is finite as an $R$-module; the $K$-span of $S$ inside $A$ is all of $A$; for every $x\in S$ the element $\Delta(x)\in A\otimes_K A$ lies in the range of the algebra map $S\otimes_R S\to A\otimes_K A$ induced by the two inclusions $S\hookrightarrow A\to A\otimes_K A$ (left and right factor); $S$ is stable under the antipode of $A$; and $\varepsilon(x)$ lies in the image of $R\to K$ for all $x\in S$. Then there exists an $R$-subalgebra $S'$ of [`CartierDual K A`](def/HopfAlgebra_CartierDual.html#L12) whose elements are exactly the functionals $\varphi$ with $\varphi(b)$ in the image of $R\to K$ for all $b\in S$, and which satisfies the same five conditions relative to the Hopf algebra [`CartierDual K A`](def/HopfAlgebra_CartierDual.html#L12): finiteness over $R$, $K$-spanning, comultiplication landing in the range of $S'\otimes_R S'\to A^\vee\otimes_K A^\vee$, stability under the antipode, and counit values in the image of $R$.
--
--   This is the statement that the dual lattice $S^\vee=\{\varphi:\varphi(S)\subseteq R\}$ of a Hopf order $S\subseteq A$ is a Hopf order in the Cartier dual $A^\vee$, the duality step in the theory of Hopf orders (prolongations of finite flat group schemes) of Tate–Oort and Raynaud. It is used in the proof of [`HopfOrder.exists_isLeast`](thm.html#HopfOrder.exists_isLeast) on the existence of a least Hopf order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_exists_dual_hopfOrder.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfOrder.exists_dual_hopfOrder
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ S' : Subalgebra R (CartierDual K A),
      (∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range) ∧
      Module.Finite R ↥S' ∧ Submodule.span K (S' : Set (CartierDual K A)) = ⊤ ∧
      (∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)).range) ∧
      (∀ x ∈ S', HopfAlgebra.antipode K (A := CartierDual K A) x ∈ S') ∧
      (∀ x ∈ S', Coalgebra.counit (R := K) (A := CartierDual K A) x ∈ (algebraMap R K).range) := by sorry
