-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_params_eventually
-- name    : IntMul.OpenAI.R154.params_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T20:39:24.855455+00:00
-- url     : https://prove2.me/theorems/a9524b4c-08a6-4855-bc3e-07c364e7b995
-- title:
--   The frozen-154 parameters satisfy the pointwise bounds for all large $n$
-- statement:
--   There is $n_1$ such that for every $n \ge n_1$, with $L(n) = \max(\lceil\log_2 n\rceil,1)$ and $p = 6L(n)$: the bit volume satisfies $0 \le V(n) \le 48n$; $p^{\varepsilon}/12 \le d(n) \le p^{\varepsilon}$; $p^{\varepsilon c}/24 \le K(n) \le p^{\varepsilon c}$; $\ell(n) \le p/(3d(n))$; and $\alpha(n) \le 4p^{1/4+\varepsilon/2}$, where $d, K, \ell, \alpha$ are the frozen-154 parameters $d = \lfloor b^{\varepsilon}\rfloor$, $K = \lfloor d^c\rfloor$, $\ell = \lceil L/d\rceil$, $\alpha = \lceil(12d^2b)^{1/4}\rceil$ and $\varepsilon = c = 2^{-51}$.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 (Table 1, eq. (fixed-parameters), margin list (margin-list)); parameters from D. Colkitt et al., integer-mult-bounds, patch frozen-154, https://github.com/CrocSwap/integer-mult-bounds/blob/main/patches/frozen-154.patch

import Mathlib
import Definitions.Def_IntMul_OpenAI_R154

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

namespace IntMul.OpenAI.R154

theorem params_eventually : ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
    IntMul.OpenAI.Glue.VP n ≤ 48 * n ∧ 0 ≤ IntMul.OpenAI.Glue.VP n ∧
      (6 * (IntMul.lg n : ℝ)) ^ ε / 12 ≤ (dP n : ℝ) ∧ (dP n : ℝ) ≤ (6 * (IntMul.lg n : ℝ)) ^ ε ∧
      (6 * (IntMul.lg n : ℝ)) ^ (ε * c) / 24 ≤ (KP n : ℝ) ∧
      (KP n : ℝ) ≤ (6 * (IntMul.lg n : ℝ)) ^ (ε * c) ∧
      (ℓP n : ℝ) ≤ 6 * (IntMul.lg n : ℝ) / (3 * (dP n : ℝ)) ∧
      (αP n : ℝ) ≤ 4 * (6 * (IntMul.lg n : ℝ)) ^ (1 / 4 + ε / 2) := by
  sorry

end IntMul.OpenAI.R154
