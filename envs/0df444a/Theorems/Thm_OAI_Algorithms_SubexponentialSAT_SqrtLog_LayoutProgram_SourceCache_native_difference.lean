-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceCache_native_difference
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_difference
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:25:29.641123+00:00
-- url     : https://prove2.me/theorems/1cefb6b8-83bc-4af5-a38f-801962e86a53
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_difference: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_difference` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceCache.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceCache.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache`, with `open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation`, `open InterpolationCacheProgram`):
--
--   ```lean
--   theorem native_difference (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
--       (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
--       (minusOne : Coeff t d) (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
--       (hQ : Q < 3^d) (i j : Fin Q) :
--       (RingProgram.modelRing t ht hd a M cache).decode ((native t a M cache minusOne).difference i j)=
--         (a.nodeUnits t Q ht hQ).differenceInverse i j
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits.differenceInverse` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRepresentedRows.NodeCache` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.node` (definitions bundle `OAIQ081S070` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.nodeUnits` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.Coeff` (definitions bundle `OAIQ081S121` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native` (definitions bundle `OAIQ081S157` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal_generated` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceCache.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_difference)

import Mathlib
import Definitions.Def_OAIQ081S157

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open InterpolationCacheProgram

variable {d Q : ℕ}

theorem native_difference (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hQ : Q < 3^d) (i j : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode ((native t a M cache minusOne).difference i j)=
      (a.nodeUnits t Q ht hQ).differenceInverse i j := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

end OAI.Algorithms
end
