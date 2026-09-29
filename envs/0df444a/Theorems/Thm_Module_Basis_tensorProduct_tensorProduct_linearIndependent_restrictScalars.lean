-- Prove2me | Theorems.Thm_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars
-- name    : Module.Basis.tensorProduct_tensorProduct_linearIndependent_restrictScalars
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/5a258dd1-5c24-5356-b9dd-39329ef7c8bb
-- title:
--   R-linear independence of a triple tensor K-basis
-- statement:
--   Let $R$, $K$ and $A$ be commutative rings with $K$ an $R$-algebra, $A$ a $K$-algebra and also an $R$-algebra, the two actions on $A$ being compatible with the $R$-action on $K$ (a scalar tower $R \subseteq K \subseteq A$). Assume that the structure map $R \to K$ is injective. Let $n$ be a natural number and let $b$ be a basis of $A$ as a $K$-module indexed by $\mathrm{Fin}\,n$. Form the tensor-product basis $b \otimes (b \otimes b)$ of the $K$-module $A \otimes_K (A \otimes_K A)$, indexed by $\mathrm{Fin}\,n \times \mathrm{Fin}\,n \times \mathrm{Fin}\,n$, whose value at $(i,j,k)$ is $b_i \otimes (b_j \otimes b_k)$. The assertion is that this family of elements of $A \otimes_K (A \otimes_K A)$, indexed by triples, is linearly independent over $R$, the $R$-module structure being the one obtained from the $K$-module structure by restriction of scalars along $R \to K$.
--
--   This is the restriction-of-scalars principle for linear independence, applied to the threefold tensor power of a finite basis: a $K$-linearly independent family stays independent over a subring mapping injectively into $K$. It is used in the construction of Hopf orders, in [`HopfAlgebra.exists_hopfOrder_of_basis_structureConstants_mem_range`](thm.html#HopfAlgebra.exists_hopfOrder_of_basis_structureConstants_mem_range), to obtain injectivity of the induced map on threefold tensor products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars.lean

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.LinearIndependent.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem Module.Basis.tensorProduct_tensorProduct_linearIndependent_restrictScalars
    (R : Type) (K : Type) (A : Type) [CommRing R] [CommRing K] [Algebra R K] [CommRing A]
    [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (hinj : Function.Injective (algebraMap R K))
    {n : ℕ} (b : Module.Basis (Fin n) K A) :
    LinearIndependent R ((b.tensorProduct (b.tensorProduct b)) :
      Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A)) := by sorry
