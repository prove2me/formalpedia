-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSourceLocality_colored_source_admissible
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:56:23.733578+00:00
-- url     : https://prove2.me/theorems/f9d28bee-9d50-4127-a610-cf10ccd64b7c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSourceLocality.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSourceLocality.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality`, with `open scoped BigOperators`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI SubexpLiftRing SubexpQuarticRing`, `open MulticolorTypes Subexp.ConstructivePacking`, `open LeafProgram LeafProgram.NodeConcrete`, `open LayoutProgram PerturbationAssembly Polynomial`):
--
--   ```lean
--   theorem colored_source_admissible (q : Factor.Spec r Q n d)
--       (H : Finset (Fin n)) (high : H → Bool)
--       (state : Fin 768 → List Bool) (ids : List ℕ) (color : ℕ → Fin r) :
--       Squarefree.Admissible
--         (∏ g : Fin r, sourceProduct q H high state (ids.filter (fun f => color f = g)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Admissible` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.sourceProduct` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSourceLocality.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog

open OAI SubexpLiftRing SubexpQuarticRing
open MulticolorTypes Subexp.ConstructivePacking
open LeafProgram LeafProgram.NodeConcrete
open LayoutProgram PerturbationAssembly Polynomial

noncomputable section

variable {r Q d n : ℕ}

theorem colored_source_admissible (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (ids : List ℕ) (color : ℕ → Fin r) :
    Squarefree.Admissible
      (∏ g : Fin r, sourceProduct q H high state (ids.filter (fun f => color f = g))) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end
