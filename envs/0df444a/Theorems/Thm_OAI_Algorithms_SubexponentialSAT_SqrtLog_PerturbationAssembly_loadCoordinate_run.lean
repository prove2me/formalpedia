-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_loadCoordinate_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:36:35.546303+00:00
-- url     : https://prove2.me/theorems/30b50948-216c-49a5-b38c-0f808b89d817
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyCoordinate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyCoordinate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor`):
--
--   ```lean
--   theorem loadCoordinate_run {n : ℕ} (s : Store) (v : Fin n) (bits rest : List Bool)
--       (hrow : s 230=true::(Encoding.frame bits++rest))
--       (hn : (s 212).length=n) (hv : (s 218).length=v.val)
--       (he : ∀ i ∈ coordinateLoadScratch, s i=[]) :
--       ExecutesIn loadCoordinate (15*bits.length+11*n+17*v.val+38) s
--         (coordinateLoaded s bits rest (Squarefree.encodeMask {v}))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeMask` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinateLoadScratch` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinateLoaded` (definitions bundle `OAIQ081S080` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate` (definitions bundle `OAIQ081S135` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyCoordinate.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S135

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

theorem loadCoordinate_run {n : ℕ} (s : Store) (v : Fin n) (bits rest : List Bool)
    (hrow : s 230=true::(Encoding.frame bits++rest))
    (hn : (s 212).length=n) (hv : (s 218).length=v.val)
    (he : ∀ i ∈ coordinateLoadScratch, s i=[]) :
    ExecutesIn loadCoordinate (15*bits.length+11*n+17*v.val+38) s
      (coordinateLoaded s bits rest (Squarefree.encodeMask {v})) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end
