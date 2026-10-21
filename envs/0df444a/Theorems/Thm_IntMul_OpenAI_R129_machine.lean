-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_machine
-- name    : IntMul.OpenAI.R129.machine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:35.93036+00:00
-- url     : https://prove2.me/theorems/55510dcb-a3cd-4d79-91c6-2aa32a53b005
-- title:
--   The OpenAI machine at the same-network-129 parameters meets the cost table
-- statement:
--   There is a multitape Turing machine $M$ (model `IntMul_MultitapeModel`) that multiplies correctly at every length $n \ge 1$, together with $C_0 \ge 0$ and $A, n_1 \in \mathbb N$, such that for every $n \ge n_1$ it multiplies $n$-bit inputs within $$C_0\Big(V(n)\,N\big(6L(n), d(n), K(n), \ell(n), \alpha(n)\big)\,(\log L(n)+1)^A + n\Big)$$ steps, where $V(n)$ is the bit volume, $N$ is the same-network-129 cost table and $d, K, \ell, \alpha$ are the same-network-129 parameters ($\varepsilon = c = 2^{-43}$).
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 (Table 1, eq. (fixed-parameters), margin list (margin-list)); parameters from D. Colkitt et al., integer-mult-bounds, patch same-network-129, https://github.com/CrocSwap/integer-mult-bounds/blob/main/patches/same-network-129.patch

import Mathlib
import Definitions.Def_IntMul_OpenAI_R129

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

namespace IntMul.OpenAI.R129

theorem machine : ∃ M : IntMul.MultitapeTM,
    (∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ A n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → IntMul.MultipliesAt M n
        (C₀ * (IntMul.OpenAI.Glue.VP n *
          Ncost (6 * (IntMul.lg n : ℝ)) (dP n) (KP n) (ℓP n) (αP n) *
            (Real.log (IntMul.lg n) + 1) ^ A + n)) := by
  sorry

end IntMul.OpenAI.R129
