-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarInitialReferenceInput_bounds
-- name    : OAI.Erdos3.scalarInitialReferenceInput_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T04:16:01.21651+00:00
-- url     : https://prove2.me/theorems/922a75a0-11d6-4c0e-a358-93aa4335b997
-- title:
--   The scalar initial reference input dominates its ingredients
-- statement:
--   Let $m, n, d \in \mathbb N$ and let $p, P_0$ be reals with $0 \le p$ and $0 \le P_0$. Put $Z =$ `replacementCommonInputLog m n d P₀`, $G = 2\,$`physicalPairCoefficientLog n d Z` $+ 2$, and $U =$ `scalarInitialReferenceInput m n d p P₀` $= G + Z + P_0 + m + n + d +$ `scalarTransferTail (3p)` $+ p + 20$, where `scalarTransferTail t` $= 2(t + 10)$ and the other two are explicit real-valued functions of OpenAI. Then $0 \le U$, $Z \le U$, $G + P_0 + 2 \le U$, $P_0 \le U$, $m \le U$, $n \le U$, $d \le U$, `scalarTransferTail (3p)` $\le U$, and $p \le U$.
--
--   Lean: `OAI.Erdos3.scalarInitialReferenceInput_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/IndexedComparableScalarGeometryData.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B165` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/IndexedComparableScalarGeometryData.lean#L51

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B165

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem scalarInitialReferenceInput_bounds (m n d : ℕ) {p P0 : ℝ} (hp : 0 ≤ p) (hP0 : 0 ≤ P0) :
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    0 ≤ U ∧ Z ≤ U ∧ G + P0 + 2 ≤ U ∧ P0 ≤ U ∧
      (m : ℝ) ≤ U ∧ (n : ℝ) ≤ U ∧ (d : ℝ) ≤ U ∧ scalarTransferTail (3 * p) ≤ U ∧ p ≤ U := by
  sorry

end Erdos3
end
end OAI
