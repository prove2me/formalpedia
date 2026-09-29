-- Prove2me | Theorems.Thm_NumberField_AdicCompletion_exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul
-- name    : NumberField.AdicCompletion.exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/81eef3d1-68e5-5d94-b276-105e7ae7bf4e
-- title:
--   Multiplicative annuli in Kᵥ lie in dilates of one compact set
-- statement:
--   Let $K$ be a number field, $\mathcal{O}_K$ its ring of integers and $v$ a point of the height-one spectrum of $\mathcal{O}_K$, i.e. a finite place; write $K_v$ for the $v$-adic completion `v.adicCompletion K` with its norm. Let $n$ be a natural number with $n > 0$ and let $R$ be a real number with $R > 0$. The assertion is that there exists a subset $B \subseteq K_v$ which is compact and does not contain $0$, and which is such that for every real $a > 0$ there is an element $x_0 \in K_v$, $x_0 \neq 0$, with
--   $$\{x \in K_v : a \le \lVert x\rVert^n \ \text{and}\ \lVert x\rVert^n \le a R\} \subseteq x_0 \cdot B,$$
--   the dilate being the pointwise scalar multiple of $B$ by $x_0$. Thus a single compact set, depending only on $K$, $v$, $n$ and $R$, absorbs all the "annuli" $a \le \lVert x\rVert^n \le aR$ of fixed multiplicative width $R$ after a suitable multiplicative translation. No nonemptiness of $B$ or of the annulus is asserted, and $x_0$ is not claimed to lie in the annulus.
--
--   This is the non-archimedean local input controlling the $K_v^\times$-direction of a fibration: annuli of bounded multiplicative width in a completion of a number field at a finite place are uniformly contained in dilates of one compact set avoiding the origin. It is used in [`AutomorphicForm.exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le`](thm.html#AutomorphicForm.exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdicCompletion_exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem NumberField.AdicCompletion.exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 < R) :
    ∃ B : Set (v.adicCompletion K), IsCompact B ∧ (0 : v.adicCompletion K) ∉ B ∧
      ∀ a : ℝ, 0 < a → ∃ x₀ : v.adicCompletion K, x₀ ≠ 0 ∧
        {x : v.adicCompletion K | a ≤ ‖x‖ ^ n ∧ ‖x‖ ^ n ≤ a * R} ⊆ x₀ • B := by sorry
