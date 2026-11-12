-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupNativeDegreeBound_nativeCompatibilityRate_eq
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:46:25.994623+00:00
-- url     : https://prove2.me/theorems/ca80c264-fc14-49d3-9e15-6c2508254e98
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq` of [lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupNativeDegreeBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupNativeDegreeBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldHistory AllFieldActiveLaws AllFieldActiveCapacity`, `open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws`, `open AllFieldGroupCountRate AllFieldGroupPairWindows AllFieldGroupPairEntropy`, `open AllFieldGroupProjectedEntropy JointCompatibilityRateLimit`, `open MatrixMultiplication.Foundation Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem nativeCompatibilityRate_eq (allocation : Allocation) (sigma : Placement)
--       (side : Fin 3) (hside : side ≠ 0) :
--       nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side =
--         orderNativeDegree (K := K) (tick := tick) allocation sigma side
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.orderNativeDegree`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Allocation` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.nativeCompatibilityRate` (definitions bundle `OAIQ254M007` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupNativeDegreeBound.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq)

import Mathlib
import Definitions.Def_OAIQ254M007

section

attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupNativeDegreeBound

open AllFieldHistory AllFieldActiveLaws AllFieldActiveCapacity
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupCountRate AllFieldGroupPairWindows AllFieldGroupPairEntropy
open AllFieldGroupProjectedEntropy JointCompatibilityRateLimit
open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem nativeCompatibilityRate_eq (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (hside : side ≠ 0) :
    nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side =
      orderNativeDegree (K := K) (tick := tick) allocation sigma side := by
  sorry

end MatrixMultiplication.AllFieldGroupNativeDegreeBound

end
end

end MatrixAllFields

end OAI
end
