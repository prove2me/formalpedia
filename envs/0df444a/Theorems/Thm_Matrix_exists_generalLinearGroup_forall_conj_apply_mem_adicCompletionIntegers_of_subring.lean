-- Prove2me | Theorems.Thm_Matrix_exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring
-- name    : Matrix.exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/d6d95100-78ac-50fd-b7b5-837c0bbc048c
-- title:
--   Bounded ℤᵥ-stable subrings of M₂(ℚᵥ) are conjugate-integral
-- statement:
--   Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$, write $\mathbb{Q}_v$ for the $v$-adic completion of $\mathbb{Q}$ and $\mathbb{Z}_v \subseteq \mathbb{Q}_v$ for its subring of elements of non-negative valuation (the $v$-adic integers). Let $O$ be a subring of the matrix ring $M_2(\mathbb{Q}_v)$ — so $O$ contains $0$ and $1$ and is closed under addition, negation and multiplication — subject to two hypotheses: first, $O$ is stable under scalar multiplication by $v$-adic integers, i.e. $r \cdot x \in O$ whenever $r \in \mathbb{Z}_v$ and $x \in O$; second, $O$ has uniformly bounded denominators, i.e. there exists $d \in \mathbb{Q}_v$ with $d \neq 0$ such that $d\,x_{ij} \in \mathbb{Z}_v$ for every $x \in O$ and all indices $i,j \in \{0,1\}$. The conclusion is that there exists $h \in \mathrm{GL}_2(\mathbb{Q}_v)$ such that for every $x \in O$ and all $i,j$ the $(i,j)$ entry of the matrix product $h^{-1} x h$ lies in $\mathbb{Z}_v$; that is, $h^{-1} O h \subseteq M_2(\mathbb{Z}_v)$, the containment being stated entrywise.
--
--   This is the local integrality statement for orders in a split quaternion algebra: any $\mathbb{Z}_v$-stable subring of $M_2(\mathbb{Q}_v)$ with bounded denominators is contained in a $\mathrm{GL}_2(\mathbb{Q}_v)$-conjugate of the standard maximal order $M_2(\mathbb{Z}_v)$. It is used in the comparison of maximal orders in a quaternion algebra with local boxes, via [`QuaternionAlgebra.IsMaximalOrder.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem Matrix.exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring
    (v : HeightOneSpectrum (𝓞 ℚ))
    (O : Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hsmul : ∀ r : v.adicCompletion ℚ, r ∈ v.adicCompletionIntegers ℚ → ∀ x ∈ O, r • x ∈ O)
    (hbdd : ∃ d : v.adicCompletion ℚ, d ≠ 0 ∧ ∀ x ∈ O, ∀ i j, d * x i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ h : GL (Fin 2) (v.adicCompletion ℚ), ∀ x ∈ O, ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * x *
        (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ := by sorry
