-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_Ncost_le
-- name    : IntMul.OpenAI.R154.Ncost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T20:38:48.161199+00:00
-- url     : https://prove2.me/theorems/46afeb8e-01f0-485c-9eec-adb1af7bc205
-- title:
--   The frozen-154 cost table is at most $50\,p^{1-2\kappa}$
-- statement:
--   Let $p \ge 1$ and let $d, K, \ell, \alpha$ be reals with $p^{\varepsilon}/12 \le d \le p^{\varepsilon}$, $p^{\varepsilon c}/24 \le K \le p^{\varepsilon c}$, $0 \le \ell \le p/(3d)$ and $0 \le \alpha \le 4p^{1/4+\varepsilon/2}$, where $\varepsilon = c = 2^{-51}$. Then the normalized cost satisfies $N(p,d,K,\ell,\alpha) \le 50\,p^{1-2\kappa}$ with $\kappa = 2^{-154}$.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 (Table 1, eq. (fixed-parameters), margin list (margin-list)); parameters from D. Colkitt et al., integer-mult-bounds, patch frozen-154, https://github.com/CrocSwap/integer-mult-bounds/blob/main/patches/frozen-154.patch

import Mathlib
import Definitions.Def_IntMul_OpenAI_R154

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

namespace IntMul.OpenAI.R154

theorem Ncost_le (p d K ℓ α : ℝ) (hp : 1 ≤ p)
    (hd1 : p ^ ε / 12 ≤ d) (hd2 : d ≤ p ^ ε)
    (hK1 : p ^ (ε * c) / 24 ≤ K) (hK2 : K ≤ p ^ (ε * c))
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ p / (3 * d))
    (hα0 : 0 ≤ α) (hα : α ≤ 4 * p ^ (1 / 4 + ε / 2)) :
    Ncost p d K ℓ α ≤ 50 * p ^ es := by
  sorry

end IntMul.OpenAI.R154
