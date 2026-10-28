-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_stageCertificate_uniformSigma
-- name    : OAI.TuringRigidity.RelativeConstructible.stageCertificate_uniformSigma
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:46:56.056718+00:00
-- url     : https://prove2.me/theorems/730e7533-a1b0-487c-a3dc-bdd8f59e59bc
-- title:
--   OAI.TuringRigidity.RelativeConstructible.stageCertificate_uniformSigma: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.stageCertificate_uniformSigma` of [lean/OAI/Computability/DegreeRigidity/Constructibility/UniformSigmaHierarchy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/UniformSigmaHierarchy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding`, `open BoundedDefinability SetModelFunctions`):
--
--   ```lean
--   theorem stageCertificate_uniformSigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
--       UniformSigmaDefinable M (fun E e =>
--         ∃ d ∈ E, ∃ f ∈ E, ∃ r ∈ E, e 1 ∈ d ∧
--           HierarchyGraph E (e 2) d r f ∧ StageStep (e 2) f r (e 1) (e 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.RelativeConstructible.StageStep` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedDefinability.UniformSigmaDefinable` and `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.HierarchyGraph` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension` and `OAI.TuringRigidity.RelativeConstructible.uniform_ordinal_definition_symmetric` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/UniformSigmaHierarchy.lean (declaration OAI.TuringRigidity.RelativeConstructible.stageCertificate_uniformSigma)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem stageCertificate_uniformSigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    UniformSigmaDefinable M (fun E e =>
      ∃ d ∈ E, ∃ f ∈ E, ∃ r ∈ E, e 1 ∈ d ∧
        HierarchyGraph E (e 2) d r f ∧ StageStep (e 2) f r (e 1) (e 0)) := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
