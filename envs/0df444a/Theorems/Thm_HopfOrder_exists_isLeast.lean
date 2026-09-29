-- Prove2me | Theorems.Thm_HopfOrder_exists_isLeast
-- name    : HopfOrder.exists_isLeast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/205b0ba1-191f-5dfb-ac79-c2ad972c2fd4
-- title:
--   Existence of a least Hopf order via Cartier duality
-- statement:
--   Let $R$ be a principal ideal domain with field of fractions $K$ of characteristic $0$, and let $A$ be a commutative ring which is a Hopf algebra over $K$, finite as a $K$-module and cocommutative, and which is an $R$-algebra compatibly with $R \to K$. Call an $R$-subalgebra $T \subseteq A$ admissible if: $T$ is finite as an $R$-module; the $K$-span of $T$ in $A$ is all of $A$; for every $x \in T$ the comultiplication $\Delta(x)$ lies in the range of the algebra map $T \otimes_R T \to A \otimes_K A$ obtained from the two inclusions $T \hookrightarrow A \rightrightarrows A \otimes_K A$ (`includeLeft` and `includeRight`, with scalars restricted to $R$); the antipode of $A$ maps $T$ into $T$; and the counit maps every $x \in T$ into the range of $\mathrm{algebraMap}\ R\ K$. The theorem asserts that if some $R$-subalgebra $S$ of $A$ is admissible, then there exists an admissible $R$-subalgebra $S_{\min}$ of $A$ with $S_{\min} \le T$ for every admissible $R$-subalgebra $T$ of $A$; that is, the set of such subalgebras, assumed non-empty, has a least element.
--
--   This is the existence of the minimal Hopf order (minimal prolongation) of a finite cocommutative Hopf algebra over a characteristic-zero fraction field, in the form used for prolongations of finite flat group schemes. It is used in the comparison of Hopf orders for objects of the associated category of finite vector space schemes, via [`HopfAlgebra.FVect.hopfOrder_eq_of_le`](thm.html#HopfAlgebra.FVect.hopfOrder_eq_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_exists_isLeast.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfOrder.exists_isLeast
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ Smin : Subalgebra R A, (Module.Finite R ↥Smin ∧ Submodule.span K (Smin : Set A) = ⊤ ∧
        (∀ x ∈ Smin, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smin.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smin.val)).range) ∧
        (∀ x ∈ Smin, HopfAlgebra.antipode K (A := A) x ∈ Smin) ∧
        (∀ x ∈ Smin, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) ∧
      ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → Smin ≤ T := by sorry
