-- Prove2me | Theorems.Thm_OAI_TuringRigidity_OrdinalCoding_vectorCode_certificates_at_levels
-- name    : OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:41:43.529104+00:00
-- url     : https://prove2.me/theorems/f07347b9-01c9-44a1-a61d-d459c4fa8568
-- title:
--   OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels` of [lean/OAI/Computability/DegreeRigidity/OrdinalCodes/VectorCodeLevels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/OrdinalCodes/VectorCodeLevels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.OrdinalCoding`, with `open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic`):
--
--   ```lean
--   theorem vectorCode_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
--       {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M) :
--       ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
--         (vectorCode v).toZFSet ∈ level (groundReals M) δ ∧
--         VectorCodeCertificates (level (groundReals M) δ) v
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.OrdinalCoding.VectorCodeCertificates`, `OAI.TuringRigidity.OrdinalCoding.vectorCode` and `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.OrdinalCoding.cofinal_padded_code_certificates` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/OrdinalCodes/VectorCodeLevels.lean (declaration OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem vectorCode_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      (vectorCode v).toZFSet ∈ level (groundReals M) δ ∧
      VectorCodeCertificates (level (groundReals M) δ) v := by
  sorry

end TuringRigidity.OrdinalCoding

end OAI
end
