-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_kappaBound_of_table
-- name    : IntMul.OpenAI.R154.kappaBound_of_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T20:39:59.56384+00:00
-- url     : https://prove2.me/theorems/e4b65472-b3f5-4eaf-a2d7-6cbcfd17ae8c
-- title:
--   A machine meeting the frozen-154 cost table gives $\mathrm{KappaBound}(2^{-154})$
-- statement:
--   Let $M$ be a multitape machine that multiplies correctly at every length $n \ge 1$. Suppose there are $n_0, A \in \mathbb N$, $C_0 \ge 0$ and real sequences $V, d, K, \ell, \alpha$ such that for all $n \ge n_0$, with $p = 6L(n)$: $0 \le V(n) \le 48n$, the pointwise bounds $p^{\varepsilon}/12 \le d(n) \le p^{\varepsilon}$, $p^{\varepsilon c}/24 \le K(n) \le p^{\varepsilon c}$, $0 \le \ell(n) \le p/(3d(n))$, $0 \le \alpha(n) \le 4p^{1/4+\varepsilon/2}$ hold, and $M$ multiplies $n$-bit inputs within $C_0\big(V(n)\,N(p, d(n), K(n), \ell(n), \alpha(n))\,(\log L(n) + 1)^A + n\big)$ steps. Then $\mathrm{KappaBound}(2^{-154})$ holds.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 (Table 1, eq. (fixed-parameters), margin list (margin-list)); parameters from D. Colkitt et al., integer-mult-bounds, patch frozen-154, https://github.com/CrocSwap/integer-mult-bounds/blob/main/patches/frozen-154.patch

import Mathlib
import Definitions.Def_IntMul_OpenAI_R154

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

namespace IntMul.OpenAI.R154

theorem kappaBound_of_table (M : IntMul.MultitapeTM)
    (hcorr : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T)
    (n₀ A : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (V d K ℓ α : ℕ → ℝ)
    (hV : ∀ n, n₀ ≤ n → V n ≤ 48 * n) (hV0 : ∀ n, n₀ ≤ n → 0 ≤ V n)
    (hd1 : ∀ n, n₀ ≤ n → (6 * (IntMul.lg n : ℝ)) ^ ε / 12 ≤ d n)
    (hd2 : ∀ n, n₀ ≤ n → d n ≤ (6 * (IntMul.lg n : ℝ)) ^ ε)
    (hK1 : ∀ n, n₀ ≤ n → (6 * (IntMul.lg n : ℝ)) ^ (ε * c) / 24 ≤ K n)
    (hK2 : ∀ n, n₀ ≤ n → K n ≤ (6 * (IntMul.lg n : ℝ)) ^ (ε * c))
    (hℓ0 : ∀ n, n₀ ≤ n → 0 ≤ ℓ n) (hℓ : ∀ n, n₀ ≤ n → ℓ n ≤ 6 * (IntMul.lg n : ℝ) / (3 * d n))
    (hα0 : ∀ n, n₀ ≤ n → 0 ≤ α n)
    (hα : ∀ n, n₀ ≤ n → α n ≤ 4 * (6 * (IntMul.lg n : ℝ)) ^ (1 / 4 + ε / 2))
    (htime : ∀ n, n₀ ≤ n → IntMul.MultipliesAt M n
      (C₀ * (V n * Ncost (6 * (IntMul.lg n : ℝ)) (d n) (K n) (ℓ n) (α n) *
        (Real.log (IntMul.lg n) + 1) ^ A + n))) :
    IntMul.KappaBound (1 / 2 ^ 154) := by
  sorry

end IntMul.OpenAI.R154
