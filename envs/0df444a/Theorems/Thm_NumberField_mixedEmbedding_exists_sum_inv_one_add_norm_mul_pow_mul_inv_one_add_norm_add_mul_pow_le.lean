-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le
-- name    : NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/0fd6ece3-38e0-5cee-8da4-b706b2c30fad
-- title:
--   Uniform decay bound for sheared two-variable lattice sums over a number field
-- statement:
--   Let $K$ be a number field, let $\mathcal{O}_K$ be its ring of integers, let $E = \mathrm{mixedSpace}\,K = \prod_{w \text{ real}} \mathbb{R} \times \prod_{w \text{ complex}} \mathbb{C}$ be its mixed space, carrying the sup norm $\|\cdot\|$ and its componentwise ring structure, let $\iota =$ `NumberField.mixedEmbedding K` be the canonical ring embedding $K \to E$, and let $\mathrm{Nm} =$ `NumberField.mixedEmbedding.norm` be the multiplicative norm on $E$ (the product of the absolute values of the components, complex components counted with multiplicity $2$). Fix a nonzero $s \in \mathcal{O}_K$ and a natural number $N$. The assertion is that there exist a natural number $M$ and a real $C \ge 0$ such that the following holds for all $a, b \in E$ with $\mathrm{Nm}(a) > 0$ and $\mathrm{Nm}(b) > 0$, for every map $\tau \colon K \to E$ (no regularity assumed) with $\tau(0) = 0$, and for every finite set $T$ of pairs $(\xi_1,\xi_2) \in K \times K$ such that each $(\xi_1,\xi_2) \in T$ is nonzero as a pair and both $s\xi_1$ and $s\xi_2$ lie in the image of $\mathcal{O}_K$ in $K$: $$\sum_{(\xi_1,\xi_2) \in T} \bigl(1 + \|a\,\iota(\xi_1)\|\bigr)^{-M}\bigl(1 + \|\tau(\xi_1) + b\,\iota(\xi_2)\|\bigr)^{-M} \le C\,\bigl(1 + \mathrm{Nm}(a)^{-2}\bigr)\bigl(1 + \mathrm{Nm}(b)^{-2}\bigr)\Bigl(\min\bigl(1, \mathrm{Nm}(a)^{-N}\bigr) + \min\bigl(1, \mathrm{Nm}(b)^{-N}\bigr)\Bigr),$$ where $M$ and $C$ depend only on $K$, $s$ and $N$, and in particular not on $a$, $b$, $\tau$ or $T$.
--
--   This is the archimedean core of the convergence and growth estimates for the two-variable theta sums attached to Schwartz–Bruhat functions on $\mathbb{A}_K^2$: the Schwartz decay of the archimedean factor is majorised by the kernel $(1+\|v_1\|)^{-M}(1+\|v_2\|)^{-M}$, the compact support of the finite factor confines the rational points to the fractional ideal $s^{-1}\mathcal{O}_K$, and the unipotent shear is absorbed by the arbitrary map $\tau$. It is used in the adelic Fourier-analytic part of the development, in [`NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact`](thm.html#NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField Classical

theorem NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le
    (K : Type) [Field K] [NumberField K] {s : 𝓞 K} (hs : s ≠ 0) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (a b : NumberField.mixedEmbedding.mixedSpace K),
        0 < NumberField.mixedEmbedding.norm a → 0 < NumberField.mixedEmbedding.norm b →
        ∀ (τ : K → NumberField.mixedEmbedding.mixedSpace K), τ 0 = 0 →
        ∀ (T : Finset (K × K)),
          (∀ p ∈ T, p ≠ 0 ∧ (∃ c : 𝓞 K, (c : K) = (s : K) * p.1) ∧
            (∃ c : 𝓞 K, (c : K) = (s : K) * p.2)) →
          ∑ p ∈ T, ((1 + ‖a * NumberField.mixedEmbedding K p.1‖) ^ M)⁻¹ *
              ((1 + ‖τ p.1 + b * NumberField.mixedEmbedding K p.2‖) ^ M)⁻¹
            ≤ C * (1 + (NumberField.mixedEmbedding.norm a)⁻¹ ^ 2)
                * (1 + (NumberField.mixedEmbedding.norm b)⁻¹ ^ 2)
                * (min 1 ((NumberField.mixedEmbedding.norm a)⁻¹ ^ N)
                    + min 1 ((NumberField.mixedEmbedding.norm b)⁻¹ ^ N)) := by sorry
