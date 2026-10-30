-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeTerminal_power_bounded
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power_bounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:04:10.45352+00:00
-- url     : https://prove2.me/theorems/ce65416d-af81-4566-9a89-ba5a04ca28ca
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power_bounded: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power_bounded` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeTerminal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeTerminal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal`, with `open BitProgram StructuredCalls`, `open scoped BigOperators`, `open DisjointReuse.DFSVisit`):
--
--   ```lean
--   theorem power_bounded (a : Data) (n bound : ℕ)
--       (hn : a.stacks 258 = Encoding.encodeNat n)
--       (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
--       (hscratch : a.stacks 269 = [])
--       (hframe : ∀ i, (a.stacks i).length ≤ bound) (hbudget : 5 * n + 6 ≤ bound) :
--       BoundedEval power (11 * n + 17) a (powered a n) bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.powered` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeTerminal.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power_bounded)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

open DisjointReuse.DFSVisit

theorem power_bounded (a : Data) (n bound : ℕ)
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
    (hscratch : a.stacks 269 = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound) (hbudget : 5 * n + 6 ≤ bound) :
    BoundedEval power (11 * n + 17) a (powered a n) bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
end
