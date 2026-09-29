-- Prove2me | Theorems.Thm_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range
-- name    : HopfAlgebra.exists_hopfOrder_of_basis_structureConstants_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/7fe69f1b-5f54-5f02-99f5-2540d87aa1f7
-- title:
--   Hopf order from a basis with R-integral structure constants
-- statement:
--   Let $R$ be a commutative ring, $K$ a field with an $R$-algebra structure such that $\operatorname{algebraMap} R \to K$ is injective, and let $A$ be a commutative ring carrying the structure of a Hopf algebra over $K$ whose comultiplication is cocommutative. Suppose given a natural number $n$ and a $K$-basis $b$ of $A$ indexed by $\mathrm{Fin}\,n$ such that all the structure constants of $A$ in this basis lie in the image of $R$ in $K$: for all $i,j,k$ the $k$-th coordinate of $b_i b_j$, for all $k$ the $k$-th coordinate of $1$, for all $i$ and all pairs $(j,k)$ the $(j,k)$-coordinate of $\Delta(b_i)$ with respect to the tensor-product basis $b\otimes b$ of $A\otimes_K A$, for all $i$ the value $\varepsilon(b_i)$, and for all $i,k$ the $k$-th coordinate of $S(b_i)$, where $\Delta$, $\varepsilon$ and $S$ denote the comultiplication, counit and antipode. Then there exists a type $H$ with a commutative ring structure and a Hopf $R$-algebra structure such that $H$ is a finite and flat $R$-module, its comultiplication is cocommutative, and there is a $K$-algebra isomorphism $\psi \colon K\otimes_R H \to A$ which is compatible with comultiplication in the sense that $\Delta(\psi x) = (\psi\otimes\psi)(\Delta x)$ for all $x$.
--
--   This is the descent of a Hopf algebra to a Hopf order (an integral $R$-form) along an injection $R\hookrightarrow K$, obtained by taking the $R$-span of a basis whose structure constants are $R$-integral; the conclusion records finiteness, flatness and cocommutativity of the order together with comultiplication-compatibility of the comparison isomorphism, counit and antipode compatibility being determined by these. It is the purely algebraic input to [`HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_basis_match`](thm.html#HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_basis_match), where it is applied with $R$ a localisation of $\mathbb{Z}$ and $K = \mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_hopfOrder_of_basis_structureConstants_mem_range
    (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (A : Type) [CommRing A] [HopfAlgebra K A] (hAcocomm : Coalgebra.IsCocomm K A)
    (n : ℕ) (b : Module.Basis (Fin n) K A)
    (hmul : ∀ i j k, b.repr (b i * b j) k ∈ (algebraMap R K).range)
    (hone : ∀ k, b.repr 1 k ∈ (algebraMap R K).range)
    (hcomul : ∀ i jk, (b.tensorProduct b).repr (Coalgebra.comul (R := K) (b i)) jk
        ∈ (algebraMap R K).range)
    (hcounit : ∀ i, Coalgebra.counit (R := K) (b i) ∈ (algebraMap R K).range)
    (hanti : ∀ i k, b.repr (HopfAlgebra.antipode K (b i)) k ∈ (algebraMap R K).range) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ ψ : (K ⊗[R] H) ≃ₐ[K] A,
        ∀ x, Coalgebra.comul (R := K) (ψ x)
          = (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := K) x) := by sorry
