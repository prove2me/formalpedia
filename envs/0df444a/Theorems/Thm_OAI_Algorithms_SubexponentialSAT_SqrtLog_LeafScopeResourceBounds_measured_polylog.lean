-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeResourceBounds_measured_polylog
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:48:39.991538+00:00
-- url     : https://prove2.me/theorems/f39c7966-aa8e-4d5b-9335-ae762c7d3d4e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeResourceBoundsPolylog.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeResourceBoundsPolylog.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds`, with `open Asymptotic LeafStatisticsProgram`):
--
--   ```lean
--   theorem measured_polylog (n m B k q : ℕ) (hn : 0 < n) (hm : m ≤ n*B)
--       (hB : B ≤ L n^q) (hsize : Nat.size m ≤ n)
--       (scopes : List (List ℕ)) (nb tb : List Bool)
--       (hnb : BinaryArithmetic.toNat nb = n)
--       (htb : BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1)
--       (hS : HighIncidenceProgram.Prepare.mass scopes ≤
--         (3*n*SparseCode.degreeBound m B+(HashSelect.loopCap n m+1)*SparseCode.distanceDenom m B+1)*k)
--       (hA : ∀ row ∈ scopes, row.length ≤ (SparseCode.degreeBound m B+SparseCode.distanceDenom m B+1)*k) :
--       let mask := forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb) n
--       (measured scopes mask).occurrence ≤ statCoefficient k q * L n^resourceExponent q ∧
--       max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered=0 then 0 else 1) ≤
--         statCoefficient k q * L n^resourceExponent q
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degreeBound` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.measured`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.arity` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Totals` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.mass` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.resourceExponent` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.statCoefficient` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.forwardMask` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cut` (definitions bundle `OAIQ081S052` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeResourceBoundsPolylog.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S039
import Definitions.Def_OAIQ081S052

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open Asymptotic LeafStatisticsProgram

theorem measured_polylog (n m B k q : ℕ) (hn : 0 < n) (hm : m ≤ n*B)
    (hB : B ≤ L n^q) (hsize : Nat.size m ≤ n)
    (scopes : List (List ℕ)) (nb tb : List Bool)
    (hnb : BinaryArithmetic.toNat nb = n)
    (htb : BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1)
    (hS : HighIncidenceProgram.Prepare.mass scopes ≤
      (3*n*SparseCode.degreeBound m B+(HashSelect.loopCap n m+1)*SparseCode.distanceDenom m B+1)*k)
    (hA : ∀ row ∈ scopes, row.length ≤ (SparseCode.degreeBound m B+SparseCode.distanceDenom m B+1)*k) :
    let mask := forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb) n
    (measured scopes mask).occurrence ≤ statCoefficient k q * L n^resourceExponent q ∧
    max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered=0 then 0 else 1) ≤
      statCoefficient k q * L n^resourceExponent q := by
  sorry

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end
