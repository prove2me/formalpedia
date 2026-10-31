-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQuerySpaceBounds_envelope_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.envelope_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:57:47.534666+00:00
-- url     : https://prove2.me/theorems/589d9eeb-6f74-4784-9a78-9abae373d108
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.envelope_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.envelope_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQuerySpaceBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQuerySpaceBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds`, with `open SqrtLog LeafParametersProgram NativeQueryInputBounds`, `open CostAssembly.Polynomial`):
--
--   ```lean
--   theorem envelope_bound : ∃ C e : ℕ,
--       ∀ (Cp dp Cn dn Cl dl Cf df N L k : ℕ) (q : LeafQueryFrontend.Query)
--         (n h t d J f B : ℕ),
--         BinaryArithmetic.toNat q.ambient = n → n ≤ N → h ≤ n →
--         t ≤ sourceCap Cn dn Cl dl N L k →
--         d ≤ sourceCap Cn dn Cl dl N L k →
--         J ≤ sourceCap Cn dn Cl dl N L k → f ≤ frontendCap Cf df L k →
--         querySpace q Cp dp Cn dn Cl dl Cf df N L k n h t d J f B ≤
--           max (envelope C e (sourceCap Cn dn Cl dl N L k+frontendCap Cf df L k+
--             preparedCap Cp dp Cn dn Cl dl Cf df N L k+4*N+6)) B
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.frontendCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.preparedCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.sourceCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.envelope` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.querySpace` (definitions bundle `OAIQ081S188` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQuerySpaceBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.envelope_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds

open SqrtLog LeafParametersProgram NativeQueryInputBounds
open CostAssembly.Polynomial

theorem envelope_bound : ∃ C e : ℕ,
    ∀ (Cp dp Cn dn Cl dl Cf df N L k : ℕ) (q : LeafQueryFrontend.Query)
      (n h t d J f B : ℕ),
      BinaryArithmetic.toNat q.ambient = n → n ≤ N → h ≤ n →
      t ≤ sourceCap Cn dn Cl dl N L k →
      d ≤ sourceCap Cn dn Cl dl N L k →
      J ≤ sourceCap Cn dn Cl dl N L k → f ≤ frontendCap Cf df L k →
      querySpace q Cp dp Cn dn Cl dl Cf df N L k n h t d J f B ≤
        max (envelope C e (sourceCap Cn dn Cl dl N L k+frontendCap Cf df L k+
          preparedCap Cp dp Cn dn Cl dl Cf df N L k+4*N+6)) B := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds
end
