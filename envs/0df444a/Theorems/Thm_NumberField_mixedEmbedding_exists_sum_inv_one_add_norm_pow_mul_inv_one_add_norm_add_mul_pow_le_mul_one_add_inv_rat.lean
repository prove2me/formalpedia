-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat
-- name    : NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/e742aef6-3c90-5e98-91b1-1fb31a6208c1
-- title:
--   Sheared two-variable lattice sum bound over ℚ
-- statement:
--   Fix a non-zero element $s$ of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ and a natural number $N$. The assertion is that there exist a natural number $M$ and a real constant $C \ge 0$ with the following uniform property. Let $a, b$ be elements of the mixed space $\mathrm{mixedSpace}\ \mathbb{Q}$ attached to $\mathbb{Q}$ (which has a single real coordinate and no complex ones, so $a$ and $b$ amount to real numbers), and suppose that $\mathrm{norm}\,a > 0$ and $\mathrm{norm}\,b > 0$, where $\mathrm{norm}$ is the product of the archimedean absolute values, i.e. here $|\cdot|$. Let $\tau : \mathbb{Q} \to \mathrm{mixedSpace}\ \mathbb{Q}$ be an arbitrary function (a shear) with $\tau(0) = 0$, subject to no regularity or growth assumption. Let $T$ be a finite set of pairs $(p_1, p_2) \in \mathbb{Q} \times \mathbb{Q}$ such that every $p \in T$ is non-zero as a pair and both $s p_1$ and $s p_2$ lie in $\mathcal{O}_{\mathbb{Q}}$, i.e. $p_1, p_2 \in \tfrac{1}{s}\mathbb{Z}$. Then, writing the image of a rational under the mixed embedding multiplicatively, $$\sum_{p \in T} \frac{1}{(1+\|a\,p_1\|)^M\,(1+\|\tau(p_1) + b\,p_2\|)^M} \le C\,(1 + (\mathrm{norm}\,a)^{-1})(1 + (\mathrm{norm}\,b)^{-1})\bigl(\min(1, (\mathrm{norm}\,a)^{-N}) + \min(1, (\mathrm{norm}\,b)^{-N})\bigr),$$ with $M$ and $C$ depending only on $s$ and $N$.
--
--   This is the elementary lattice-counting estimate underlying majorisation of two-variable theta-type sums over $\mathbb{Q}$: the exponent $M$ is chosen large enough, depending on the denominator $s$ and the desired decay order $N$, that a sheared sum over a scaled copy of $\mathbb{Z}^2$ is dominated by the stated product of blow-up and decay factors, uniformly in the shear $\tau$ and in the finite subset $T$. It is used in the proof of [`NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat`](thm.html#NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat), the corresponding bound for sums of Schwartz–Bruhat functions twisted by matrix action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField Classical

theorem NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat
    {s : 𝓞 ℚ} (hs : s ≠ 0) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (a b : NumberField.mixedEmbedding.mixedSpace ℚ),
        0 < NumberField.mixedEmbedding.norm a → 0 < NumberField.mixedEmbedding.norm b →
        ∀ (τ : ℚ → NumberField.mixedEmbedding.mixedSpace ℚ), τ 0 = 0 →
        ∀ (T : Finset (ℚ × ℚ)),
          (∀ p ∈ T, p ≠ 0 ∧ (∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * p.1) ∧
            (∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * p.2)) →
          ∑ p ∈ T, ((1 + ‖a * NumberField.mixedEmbedding ℚ p.1‖) ^ M)⁻¹ *
              ((1 + ‖τ p.1 + b * NumberField.mixedEmbedding ℚ p.2‖) ^ M)⁻¹
            ≤ C * (1 + (NumberField.mixedEmbedding.norm a)⁻¹)
                * (1 + (NumberField.mixedEmbedding.norm b)⁻¹)
                * (min 1 ((NumberField.mixedEmbedding.norm a)⁻¹ ^ N)
                    + min 1 ((NumberField.mixedEmbedding.norm b)⁻¹ ^ N)) := by sorry
