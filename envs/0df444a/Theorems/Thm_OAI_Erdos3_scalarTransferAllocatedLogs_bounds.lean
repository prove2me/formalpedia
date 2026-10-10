-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarTransferAllocatedLogs_bounds
-- name    : OAI.Erdos3.scalarTransferAllocatedLogs_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T03:43:14.816204+00:00
-- url     : https://prove2.me/theorems/4eb871de-c8f2-4a10-b967-a1eae2c0eb57
-- title:
--   Nonnegativity and lower bounds for the scalar transfer cap, accuracy and cell logs
-- statement:
--   Let $b \in \mathbb N$ and let $\mathrm{common}, p, Z, U$ be nonnegative reals. Write $\mathrm{cap} =$ `scalarTransferCapLog b Z` $= b(Z+2) + 1$, $\mathrm{acc} =$ `scalarTransferAccuracyLog b p Z` $= 3p + \mathrm{cap} + 10$, and $\mathrm{cell} =$ `scalarTransferCellLog common b p Z U` $= 65536(\mathrm{common}+3)^4 + Zb + \mathrm{acc} + U + 1$ (explicit real-valued functions of OpenAI). Then $0 \le \mathrm{cap}$, $0 \le \mathrm{acc}$, $0 \le \mathrm{cell}$, $65536(\mathrm{common}+3)^4 \le \mathrm{cell}$, $Zb + \mathrm{acc} + U + 1 \le \mathrm{cell}$, and $Zb + U + 1 \le \mathrm{cell}$.
--
--   Lean: `OAI.Erdos3.scalarTransferAllocatedLogs_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/IndexedComparableScalarGeometryData.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B165` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/IndexedComparableScalarGeometryData.lean#L20

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B165

namespace OAI

section

namespace Erdos3

theorem scalarTransferAllocatedLogs_bounds (b : ℕ) {common p Z U : ℝ}
    (hcommon : 0 ≤ common) (hp : 0 ≤ p) (hZ : 0 ≤ Z) (hU : 0 ≤ U) :
    0 ≤ scalarTransferCapLog b Z ∧ 0 ≤ scalarTransferAccuracyLog b p Z ∧
    0 ≤ scalarTransferCellLog common b p Z U ∧
    65536 * (common + 3) ^ 4 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + scalarTransferAccuracyLog b p Z + U + 1 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + U + 1 ≤ scalarTransferCellLog common b p Z U := by
  sorry

end Erdos3
end
end OAI
