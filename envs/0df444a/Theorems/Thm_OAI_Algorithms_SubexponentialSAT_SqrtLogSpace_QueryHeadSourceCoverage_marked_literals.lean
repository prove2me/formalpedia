-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryHeadSourceCoverage_marked_literals
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:59:14.111945+00:00
-- url     : https://prove2.me/theorems/1d2c7701-5529-4f57-816a-3817bfbf5cef
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadSourceCoverage.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadSourceCoverage.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing`, `open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram`, `open SignatureTupleSourceAlignment`):
--
--   ```lean
--   theorem marked_literals :
--       (spec).marked = true → (AssignmentConcrete.weightedHashes spec).length ∈ List.range (s).N →
--         ∀ l ∈ (spec).markedClause, l.variable ∉ H →
--           (l.variable.val,(s).n+(AssignmentConcrete.weightedHashes spec).length) ∈ (spec).ps
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` and `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Data` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Produced` (definitions bundle `OAIQ081S166` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.packingProblem` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete.weightedHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.markedClause` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.queryInputsAddressed` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts.addressedSource` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.sourceSpec` (definitions bundle `OAIQ081S188` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_target` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadSourceCoverage.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram
open SignatureTupleSourceAlignment
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
variable (physical : Data)
  (ready : Native.Ready (Native.queryInputsAddressed q k hg first tail node) physical)
  (bound : ℕ) (bounded : OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound bound physical)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height
    (unary (Native.queryInputsAddressed q k hg first tail node).R)
    (Native.queryInputsAddressed q k hg first tail node).width words)

local notation "src" => QueryHeadSourceFacts.addressedSource q k hg first tail node physical ready bound bounded ra rd rc words hc
section Factor
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed q k hg first tail node).Q < 3^(m.val 34))
    (hv : q.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
  hfield q hv hJ source hsource
local notation "H" => HighMarkedFrontend.highSet q

theorem marked_literals :
    (spec).marked = true → (AssignmentConcrete.weightedHashes spec).length ∈ List.range (s).N →
      ∀ l ∈ (spec).markedClause, l.variable ∉ H →
        (l.variable.val,(s).n+(AssignmentConcrete.weightedHashes spec).length) ∈ (spec).ps := by
  sorry

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage
end
end
