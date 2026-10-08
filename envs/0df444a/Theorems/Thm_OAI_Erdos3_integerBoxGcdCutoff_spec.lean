-- Prove2me | Theorems.Thm_OAI_Erdos3_integerBoxGcdCutoff_spec
-- name    : OAI.Erdos3.integerBoxGcdCutoff_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:46:17.497988+00:00
-- url     : https://prove2.me/theorems/242a4a2c-56b4-4f3a-8701-8cb66228961d
-- title:
--   integerBoxGcdCutoff is positive and makes 2^(d−1)(1+C)/cutoff at most ε/2
-- statement:
--   Let $d$ be a natural number and $C,\varepsilon$ real numbers with $0<\varepsilon$. Write $K$ for `integerBoxGcdCutoff d C epsilon`, the natural number $\big\lceil 2\cdot 2^{d-1}(1+C)/\varepsilon\big\rceil+1$ (natural-number ceiling; $d-1$ is natural-number subtraction). Then $0<K$ and
--   $$\frac{2^{d-1}(1+C)}{K}\le\frac{\varepsilon}{2}.$$
--
--   Lean: `OAI.Erdos3.integerBoxGcdCutoff_spec` in `lean/OAI/Combinatorics/Progressions/Lattices/IntegerBoxCutoffLogBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B009` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/IntegerBoxCutoffLogBounds.lean#L21

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

namespace OAI

section

namespace Erdos3

theorem integerBoxGcdCutoff_spec (d : ℕ) {C epsilon : ℝ}
    (heps : 0 < epsilon) :
    0 < integerBoxGcdCutoff d C epsilon ∧
      (2 : ℝ) ^ (d - 1) * (1 + C) / integerBoxGcdCutoff d C epsilon ≤ epsilon / 2 := by
  sorry

end Erdos3
end
end OAI
