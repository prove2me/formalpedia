-- Prove2me | Theorems.Thm_OAI_Erdos3_integerBoxRetainedGap_spec
-- name    : OAI.Erdos3.integerBoxRetainedGap_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:27:37.408624+00:00
-- url     : https://prove2.me/theorems/02e37aca-9433-40bb-a2a7-f1de7a7a064f
-- title:
--   integerBoxRetainedGap is positive and its multiple of L is at most D(⌊ρM⌋+1)
-- statement:
--   Let $d,D$ be natural numbers and $c,\varepsilon,L,M$ real numbers, with $0<D$, $0<c$, $0<\varepsilon$ and $cL\le M$. Write $\rho$ for `integerBoxNearRatio d epsilon`, the real number $\min\big(1,\ \varepsilon/(1+2\cdot 3^d)\big)$ (OpenAI's `replacementAccuracy (2 * 3 ^ d) epsilon`), and $g$ for `integerBoxRetainedGap d D c epsilon`, the real number $D\rho c$. Then $0<g$ and
--   $$g\cdot L\le D\cdot\big(\lfloor \rho M\rfloor+1\big),$$
--   where $\lfloor\cdot\rfloor$ is the natural-number floor.
--
--   Lean: `OAI.Erdos3.integerBoxRetainedGap_spec` in `lean/OAI/Combinatorics/Progressions/Lattices/IntegerBoxCutoffLogBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B009` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/IntegerBoxCutoffLogBounds.lean#L67

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

namespace OAI

section

namespace Erdos3

theorem integerBoxRetainedGap_spec (d D : ℕ) {c epsilon L M : ℝ}
    (hD : 0 < D) (hc : 0 < c) (heps : 0 < epsilon) (hside : c * L ≤ M) :
    0 < integerBoxRetainedGap d D c epsilon ∧
      integerBoxRetainedGap d D c epsilon * L ≤
        (D : ℝ) * (⌊integerBoxNearRatio d epsilon * M⌋₊ + 1 : ℕ) := by
  sorry

end Erdos3
end
end OAI
