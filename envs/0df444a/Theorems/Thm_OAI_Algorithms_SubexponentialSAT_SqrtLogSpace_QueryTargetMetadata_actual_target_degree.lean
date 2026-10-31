-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTargetMetadata_actual_target_degree
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:00:14.982781+00:00
-- url     : https://prove2.me/theorems/509afc0b-d096-4b7b-bb03-5794e24d19be
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTargetMetadata.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTargetMetadata.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata`, with `open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram`, `open LeafProgram.PreparedSource LeafProgram.NodeConcrete`):
--
--   ```lean
--   theorem actual_target_degree (hwidth : ∀ c ∈ source, c.length ≤ k)
--       (H : Finset (Fin (s).n)) (high : H → Bool) :
--       (specTarget spec H high).natDegree < (s).Q * (m).val 42
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Data` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Produced` (definitions bundle `OAIQ081S166` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.packingProblem` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.heads` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.numeric` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.specTarget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.nativeSpecOfInputs` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.ring_degree_pos` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.ring_precision_pos` (definitions bundle `OAIQ081S182` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.numeric_field` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.numeric_order_pos` (definitions bundle `OAIQ081S188` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTargetMetadata.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Definitions.Def_OAIQ081S188

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram
open LeafProgram.PreparedSource LeafProgram.NodeConcrete

attribute [local irreducible] Execute.guardedModel

section Addressed

variable (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ)
    (hg : Guard (q.input k))
    (first : MulticolorTypes.Word (Query.packingProblem q k hg).r
      (Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem q k hg).r
      (Query.packingProblem q k hg).Q))
    (node : Fin (Query.packingProblem q k hg).Q) (lengths : Fin 8 → ℕ)

local notation "s" => heads q k hg first tail node
local notation "m" => numeric q k lengths
local notation "ht" => Query.ring_precision_pos (q.input k) lengths hg
local notation "hd" => Query.ring_degree_pos (q.input k) lengths hg

variable (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (heads q k hg first tail node).height
      (LeafHeadSetupProgram.unary (heads q k hg first tail node).R)
      (heads q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((numeric q k lengths).val 33))
    (cache : RingProgram.ScalarCache 3 ((numeric q k lengths).val 33))
    (half : RingProgram.ScalarCode 3 ((numeric q k lengths).val 33))
    (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced (numeric q k lengths)
      (Query.ring_degree_pos (q.input k) lengths hg) M cache half e)
    (source : List (List (SAT.Literal (Fin (heads q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  (numeric_field q k lengths hg) q hv (Circuit.Model.val m 42)
  (numeric_order_pos q k lengths hg) source hsource

theorem actual_target_degree (hwidth : ∀ c ∈ source, c.length ≤ k)
    (H : Finset (Fin (s).n)) (high : H → Bool) :
    (specTarget spec H high).natDegree < (s).Q * (m).val 42 := by
  sorry

end Addressed

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata
end
end
