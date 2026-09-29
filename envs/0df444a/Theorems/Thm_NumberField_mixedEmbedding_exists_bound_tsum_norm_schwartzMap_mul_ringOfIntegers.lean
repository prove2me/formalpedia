-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers
-- name    : NumberField.mixedEmbedding.exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/0d542523-a579-5c03-bcb9-c31e9ee1f4f9
-- title:
--   Uniform bound for Schwartz sums over nonzero integers
-- statement:
--   Let $K$ be a number field and let $V$ be a normed additive commutative group which is a normed space over $\mathbb{R}$, and fix $N \in \mathbb{N}$. The assertion is the existence of an index $M \in \mathbb{N}$ and a constant $C \in \mathbb{R}$ with $0 \le C$ such that, for every Schwartz function $\Phi$ from the mixed space `NumberField.mixedEmbedding.mixedSpace K` (the product of a copy of $\mathbb{R}$ for each real place and of $\mathbb{C}$ for each complex place of $K$, with its componentwise ring structure) to $V$, and for every element $a$ of that mixed space whose mixed norm satisfies $1 \le \mathrm{Nm}(a)$, two things hold: first, the family $\xi \mapsto \lVert \Phi(a \cdot \iota(\xi)) \rVert$ indexed by the full ring of integers $\mathcal{O}_K$ is summable, where $\iota$ denotes `NumberField.mixedEmbedding K` applied to the image of $\xi$ in $K$; second, the sum of $\lVert \Phi(a \cdot \iota(\xi)) \rVert$ over the subtype of nonzero $\xi \in \mathcal{O}_K$ is at most $C \cdot p_{M,0}(\Phi) \cdot \mathrm{Nm}(a)^{-N}$, with $p_{M,0}(\Phi) =$ `SchwartzMap.seminorm ℝ M 0 Φ` the Schwartz seminorm measuring $\sup_v \lVert v \rVert^{M} \lVert \Phi(v) \rVert$ (no derivatives). Note that $M$ and $C$ are uniform in $\Phi$ and in $a$, depending only on $K$, $V$ and $N$.
--
--   This is the archimedean lattice-point estimate showing that a Schwartz function on the mixed space of $K$, dilated by an element of mixed norm at least one, has theta-type sums over the nonzero integers decaying like an arbitrarily large negative power of that norm. It is used to bound the nonzero Fourier modes of such dilated functions, in [`NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers`](thm.html#NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField Classical

theorem NumberField.mixedEmbedding.exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers
    (K : Type*) [Field K] [NumberField K]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (Φ : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) V)
        (a : NumberField.mixedEmbedding.mixedSpace K),
        1 ≤ NumberField.mixedEmbedding.norm a →
          Summable (fun ξ : 𝓞 K => ‖Φ (a * NumberField.mixedEmbedding K (ξ : K))‖) ∧
          ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖Φ (a * NumberField.mixedEmbedding K ((ξ : 𝓞 K) : K))‖ ≤
            C * SchwartzMap.seminorm ℝ M 0 Φ * (NumberField.mixedEmbedding.norm a)⁻¹ ^ N := by sorry
