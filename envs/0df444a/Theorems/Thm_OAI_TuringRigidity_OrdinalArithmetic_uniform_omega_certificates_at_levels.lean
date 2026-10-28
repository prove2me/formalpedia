-- Prove2me | Theorems.Thm_OAI_TuringRigidity_OrdinalArithmetic_uniform_omega_certificates_at_levels
-- name    : OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:49:42.171699+00:00
-- url     : https://prove2.me/theorems/5ff98f1b-249c-452d-8ca8-e34790fb2f7c
-- title:
--   OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels` of [lean/OAI/Computability/DegreeRigidity/Constructibility/UniformOmegaLevels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/UniformOmegaLevels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.OrdinalArithmetic`, with `open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible`, `open BoundedDefinability SetModelFunctions SentenceCoding`):
--
--   ```lean
--   theorem uniform_omega_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
--       (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
--       ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
--         ∀ c ≤ a, c.toZFSet ∈ level (groundReals M) δ ∧
--           (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) δ ∧
--           OmegaPowerCertificates (level (groundReals M) δ) c.toZFSet ∧
--           ∀ z ∈ level (groundReals M) δ,
--             omegaPowerSentence.Sat (level (groundReals M) δ : Set ZFSet)
--               (cons z (fun _ => c.toZFSet)) ↔ z = (Ordinal.omega0 ^ c).toZFSet
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.BoundedSetTheory.cons` and `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.OrdinalArithmetic.OmegaPowerCertificates` and `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.Sat` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.OrdinalArithmetic.omegaPowerSentence` (definitions bundle `OAIQ064A008` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.OrdinalArithmetic.internal_explicit_omega_threshold` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/UniformOmegaLevels.lean (declaration OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem uniform_omega_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      ∀ c ≤ a, c.toZFSet ∈ level (groundReals M) δ ∧
        (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) δ ∧
        OmegaPowerCertificates (level (groundReals M) δ) c.toZFSet ∧
        ∀ z ∈ level (groundReals M) δ,
          omegaPowerSentence.Sat (level (groundReals M) δ : Set ZFSet)
            (cons z (fun _ => c.toZFSet)) ↔ z = (Ordinal.omega0 ^ c).toZFSet := by
  sorry

end TuringRigidity.OrdinalArithmetic

end OAI
end
