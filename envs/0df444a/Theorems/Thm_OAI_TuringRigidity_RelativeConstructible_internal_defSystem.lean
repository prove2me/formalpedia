-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_internal_defSystem
-- name    : OAI.TuringRigidity.RelativeConstructible.internal_defSystem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:45:39.833591+00:00
-- url     : https://prove2.me/theorems/01974c60-1e79-4e3e-8e23-dc872ed97bd1
-- title:
--   OAI.TuringRigidity.RelativeConstructible.internal_defSystem: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.internal_defSystem` of [lean/OAI/Computability/DegreeRigidity/Constructibility/DefSystemCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/DefSystemCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding`, `open BoundedDefinability SetModelFunctions`):
--
--   ```lean
--   theorem internal_defSystem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
--       (Q B A : ZFSet.{u}) (hA : A ∈ M)
--       (hQ : ∀ p : SentenceForm, family p ∈ Q)
--       (hB : ∀ p : SentenceForm, supportGraph p ∈ B) :
--       ∃ G ∈ M, ∃ T ∈ M, ∃ H ∈ M, ∃ Z ∈ M,
--         DefSystem Q B A G T H Z (definablePower A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ElementaryModel.SentenceForm` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.DefSystem`, `OAI.TuringRigidity.RelativeConstructible.definablePower`, `OAI.TuringRigidity.SentenceCoding.family` and `OAI.TuringRigidity.SentenceCoding.supportGraph` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.RelativeConstructible.hierarchyGraph_sigmaDefinable` and `OAI.TuringRigidity.RelativeConstructible.stageCertificate_uniformSigma` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/DefSystemCertificate.lean (declaration OAI.TuringRigidity.RelativeConstructible.internal_defSystem)

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

theorem internal_defSystem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (Q B A : ZFSet.{u}) (hA : A ∈ M)
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) :
    ∃ G ∈ M, ∃ T ∈ M, ∃ H ∈ M, ∃ Z ∈ M,
      DefSystem Q B A G T H Z (definablePower A) := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
