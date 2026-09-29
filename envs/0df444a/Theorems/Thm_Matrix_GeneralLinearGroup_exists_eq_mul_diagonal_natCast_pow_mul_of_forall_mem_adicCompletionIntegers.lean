-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
-- name    : Matrix.GeneralLinearGroup.exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/75aa618f-0d09-5dcd-93ae-d23e56141ab6
-- title:
--   Integral Cartan decomposition at a place over ℓ
-- statement:
--   Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$, let $\ell$ be a prime natural number whose image in $\mathcal{O}_{\mathbb{Q}}$ lies in the prime ideal of $v$, and let $Y$ be an invertible $2\times 2$ matrix over the completion $\mathbb{Q}_v$ all of whose entries lie in the valuation ring $\mathcal{O}_v$ of $v$-adic integers. The assertion is that there exist natural numbers $e_1, e_2$ and elements $k_1, k_2$ of $\mathrm{GL}_2(\mathbb{Q}_v)$ such that $e_1 \le e_2$; all entries of $k_1$, of $k_1^{-1}$, of $k_2$ and of $k_2^{-1}$ lie in $\mathcal{O}_v$ (this is how membership in $\mathrm{GL}_2(\mathcal{O}_v)$ is spelled); the matrix underlying $Y$ equals the product $k_1 \cdot \mathrm{diag}(\ell^{e_1}, \ell^{e_2}) \cdot k_2$, where $\ell$ denotes the image of the natural number $\ell$ in $\mathbb{Q}_v$; and, in addition, all entries of the scalar multiple $\ell^{-1} \cdot Y$ lie in $\mathcal{O}_v$ if and only if $1 \le e_1$. Since $e_1, e_2$ are natural numbers, the exponents are automatically non-negative.
--
--   This is the elementary divisor (Smith normal form) theorem over the discrete valuation ring $\mathcal{O}_v$, in the shape of the Cartan decomposition $\mathrm{GL}_2(\mathcal{O}_v)\,\{\mathrm{diag}(\ell^{e_1},\ell^{e_2})\}\,\mathrm{GL}_2(\mathcal{O}_v)$ for integral matrices, with the uniformiser taken to be $\ell$ and supplemented by the primitivity criterion that an integral matrix is divisible by $\ell$ exactly when the smaller elementary divisor is positive. It refines the general valuation-ring statement [`Matrix.GeneralLinearGroup.exists_eq_smul_mul_diagonal_mul_of_valuationSubring`](thm.html#Matrix.GeneralLinearGroup.exists_eq_smul_mul_diagonal_mul_of_valuationSubring), and is used in the analysis of the coset graph and of local orders in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

theorem Matrix.GeneralLinearGroup.exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
    (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Y : GL (Fin 2) (v.adicCompletion ℚ))
    (hY : ∀ i j, (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ (e₁ e₂ : ℕ) (k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ)), e₁ ≤ e₂ ∧
      (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ) ∧
      (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ) ∧
      (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        Matrix.diagonal ![((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₁, ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₂] * (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
      ((∀ i j, ((((ℓ : ℕ) : v.adicCompletion ℚ)⁻¹ • (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)) ↔ 1 ≤ e₁) := by sorry
