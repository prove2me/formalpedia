-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_origin_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:07:18.641951+00:00
-- url     : https://prove2.me/theorems/984a3209-4b72-4d9a-aeeb-fc28f8247cd4
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyOrigin.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyOrigin.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives`):
--
--   ```lean
--   theorem origin_run (s : Store) (n : ℕ) (hn : (s 212).length=n)
--       (he : ∀ i ∈ originScratch,s i=[]) :
--       ExecutesIn origin (33*n+20*(s 220).length+83) s
--         (Function.update s 217 (Encoding.frame (originKey n)++Encoding.frame (s 220)++s 217))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.originScratch` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.originKey` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin` (definitions bundle `OAIQ081S150` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyOrigin.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S150

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

theorem origin_run (s : Store) (n : ℕ) (hn : (s 212).length=n)
    (he : ∀ i ∈ originScratch,s i=[]) :
    ExecutesIn origin (33*n+20*(s 220).length+83) s
      (Function.update s 217 (Encoding.frame (originKey n)++Encoding.frame (s 220)++s 217)) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end
