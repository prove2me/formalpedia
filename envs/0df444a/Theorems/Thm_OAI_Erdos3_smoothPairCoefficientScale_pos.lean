-- Prove2me | Theorems.Thm_OAI_Erdos3_smoothPairCoefficientScale_pos
-- name    : OAI.Erdos3.smoothPairCoefficientScale_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:26:48.677815+00:00
-- url     : https://prove2.me/theorems/b63fdb2b-265d-42f5-b408-f3ab11474618
-- title:
--   Smooth pair coefficient scales are positive
-- statement:
--   Let $J$ be a type and $H,L$ reals with $0<H$ and $0<L$. Then for every $c\in\mathrm{Option}\,J$, $0<$ `smoothPairCoefficientScale H L c`, where `smoothPairCoefficientScale H L` is the function on $\mathrm{Option}\,J$ sending `none` to $H$ and every `some j` to $H/L$.
--
--   Lean: `OAI.Erdos3.smoothPairCoefficientScale_pos` in `lean/OAI/Combinatorics/Progressions/Probability/AnisotropicSmoothPairLaw.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AnisotropicSmoothPairLaw.lean#L74

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem smoothPairCoefficientScale_pos {J : Type*} {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    ∀ c : Option J, 0 < smoothPairCoefficientScale H L c := by
  sorry

end Erdos3
end
end OAI
