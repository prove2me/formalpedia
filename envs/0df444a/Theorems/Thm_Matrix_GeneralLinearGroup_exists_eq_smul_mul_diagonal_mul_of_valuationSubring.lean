-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring
-- name    : Matrix.GeneralLinearGroup.exists_eq_smul_mul_diagonal_mul_of_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/54770a2a-681e-51fe-b544-1a0cf71351b1
-- title:
--   Cartan decomposition of GL₂(K) over a valuation subring
-- statement:
--   Let $K$ be a field, let $O$ be a valuation subring of $K$, and let $H$ be an element of the general linear group $\mathrm{GL}_2(K)$ of $2\times 2$ matrices indexed by `Fin 2`. The assertion is that there exist scalars $s,t \in K$ and elements $k_1,k_2 \in \mathrm{GL}_2(K)$ such that: $s \neq 0$; $t \neq 0$ and $t$ lies in $O$; every entry of the matrix underlying $k_1$ lies in $O$, and likewise every entry of the matrix underlying $k_1^{-1}$; the same two conditions hold for $k_2$ and $k_2^{-1}$; and the matrix underlying $H$ equals the scalar multiple by $s$ of the product $k_1 \cdot \operatorname{diagonal}(1,t) \cdot k_2$, the middle factor being the diagonal matrix with entries given by the vector $(1,t)$. Thus $H = s\,k_1 \operatorname{diag}(1,t)\, k_2$ with $k_1,k_2$ in $\mathrm{GL}_2(O)$ in the sense that both they and their inverses have entries in $O$. No discreteness hypothesis is imposed on the valuation, and $t$ is only required to be a nonzero element of $O$, not a power of a uniformiser.
--
--   This is the rank-two Cartan, or elementary-divisor, decomposition $\mathrm{GL}_2(K) = K^{\times}\,\mathrm{GL}_2(O)\,\{\operatorname{diag}(1,t)\}\,\mathrm{GL}_2(O)$ over an arbitrary valuation subring. It is used to normalise matrices over the completions of a number field, and thereby a connecting element between two maximal orders in a split quaternion algebra, by [`Matrix.GeneralLinearGroup.exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers`](thm.html#Matrix.GeneralLinearGroup.exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers) and by [`QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq`](thm.html#QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem Matrix.GeneralLinearGroup.exists_eq_smul_mul_diagonal_mul_of_valuationSubring
    {K : Type*} [Field K] (O : ValuationSubring K) (H : GL (Fin 2) K) :
    ∃ (s t : K) (k₁ k₂ : GL (Fin 2) K), s ≠ 0 ∧ t ≠ 0 ∧ t ∈ O ∧
      (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, ((k₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, ((k₂⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (H : Matrix (Fin 2) (Fin 2) K) =
        s • ((k₁ : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![(1 : K), t] * (k₂ : Matrix (Fin 2) (Fin 2) K)) := by sorry
