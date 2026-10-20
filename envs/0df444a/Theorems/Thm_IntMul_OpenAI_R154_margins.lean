-- Prove2me | Theorems.Thm_IntMul_OpenAI_R154_margins
-- name    : IntMul.OpenAI.R154.margins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T20:38:18.112837+00:00
-- url     : https://prove2.me/theorems/bb267ae3-5857-4f97-ad9f-9c4da2c218dd
-- title:
--   The seven cost margins at the frozen-154 constants are at least $2\kappa$
-- statement:
--   At $\tau = 1-2^{-50}$, $\delta = 1/16$, $c = \varepsilon = 2^{-51}$, $\lambda' = 1-2^{-102}$ and $\kappa = 2^{-154}$, each of the seven margins $1-\varepsilon(1+c)$, $\varepsilon c(1-\tau)$, $\varepsilon(1-\lambda')$, $1-\tau-\varepsilon(2-\tau)$, $\tfrac14-\delta-\tfrac{3\varepsilon}{2}$, $1-\delta-\varepsilon$ and $\varepsilon$ is at least $2\kappa$. Moreover $\tau(1 + 2c) < \lambda' < 1$ and $\lambda' - \tau - c > 0$.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 (Table 1, eq. (fixed-parameters), margin list (margin-list)); parameters from D. Colkitt et al., integer-mult-bounds, patch frozen-154, https://github.com/CrocSwap/integer-mult-bounds/blob/main/patches/frozen-154.patch

import Mathlib
import Definitions.Def_IntMul_OpenAI_R154

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

namespace IntMul.OpenAI.R154

theorem margins :
    2 * κ ≤ 1 - ε * (1 + c) ∧ 2 * κ ≤ ε * c * (1 - τ) ∧ 2 * κ ≤ ε * (1 - lam') ∧
      2 * κ ≤ 1 - τ - ε * (2 - τ) ∧ 2 * κ ≤ 1 / 4 - δ - 3 * ε / 2 ∧ 2 * κ ≤ 1 - δ - ε ∧
      2 * κ ≤ ε ∧ τ * (1 + c / (1 / 2)) < lam' ∧ lam' < 1 ∧ 0 < lam' - τ - c := by
  sorry

end IntMul.OpenAI.R154
