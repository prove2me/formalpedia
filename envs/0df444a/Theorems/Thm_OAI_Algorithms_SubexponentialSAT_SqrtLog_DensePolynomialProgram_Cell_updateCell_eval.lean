-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Cell_updateCell_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:26:51.484355+00:00
-- url     : https://prove2.me/theorems/e3d21b59-e1d6-4fb7-9dc0-d9828ca087f0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/DensePolynomialProgramCell.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/DensePolynomialProgramCell.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives`, `open SubexponentialSAT.SubexpJetCellProgram`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem updateCell_eval (d : Data) (a b : Coeff (baseWidth p t) degree)
--       (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
--       (frame : Fin 6 → List Bool)
--       (hs : d.stacks 102 = earlier.flatten ++ (RingProgram.flat b ++ rest))
--       (hi : d.stacks 103 = indexWord) (hiLen : indexWord.length = earlier.length)
--       (hw : d.stacks 104 = widthWord) (hwLen : widthWord.length = degree * baseWidth p t)
--       (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
--       (hscalarWidth : scalarWidth.length = baseWidth p t)
--       (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
--         (DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
--           (RingProgram.flat a) [] scalarWidth [] frame).stacks i)
--       (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = [])
--       (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
--       (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) (h118 : d.stacks 118 = []) :
--       ∃ n ≤ eventBudget degree (baseWidth p t) indexWord.length, ∃ e : Data,
--         Eval updateCell n d e ∧
--         e.stacks = Function.update (Function.update d.stacks 8 []) 102
--           (earlier.flatten ++
--             (RingProgram.flat (ops.addRun a b).1 ++ rest)) ∧
--         (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpJetCellProgram.regPorts`, `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpJetCellProgram.scalarPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.eventBudget` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.DensePolynomialLoop.ready` and `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.addRun` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpJetCellProgram.Data` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarProgram` (definitions bundle `OAIQ081S068` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.Coeff` (definitions bundle `OAIQ081S117` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/DensePolynomialProgramCell.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval)

import Mathlib
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S117

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpJetCellProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hB : 0 < baseWidth p t)
    {degree : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)

include cache hB hadd in
theorem updateCell_eval (d : Data) (a b : Coeff (baseWidth p t) degree)
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hs : d.stacks 102 = earlier.flatten ++ (RingProgram.flat b ++ rest))
    (hi : d.stacks 103 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hw : d.stacks 104 = widthWord) (hwLen : widthWord.length = degree * baseWidth p t)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hscalarWidth : scalarWidth.length = baseWidth p t)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
        (RingProgram.flat a) [] scalarWidth [] frame).stacks i)
    (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = [])
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) (h118 : d.stacks 118 = []) :
    ∃ n ≤ eventBudget degree (baseWidth p t) indexWord.length, ∃ e : Data,
      Eval updateCell n d e ∧
      e.stacks = Function.update (Function.update d.stacks 8 []) 102
        (earlier.flatten ++
          (RingProgram.flat (ops.addRun a b).1 ++ rest)) ∧
      (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i)) := by
  sorry

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

end OAI.Algorithms
end
