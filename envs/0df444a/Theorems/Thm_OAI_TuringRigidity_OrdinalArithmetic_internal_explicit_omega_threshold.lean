-- Prove2me | Theorems.Thm_OAI_TuringRigidity_OrdinalArithmetic_internal_explicit_omega_threshold
-- name    : OAI.TuringRigidity.OrdinalArithmetic.internal_explicit_omega_threshold
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:40:27.63992+00:00
-- url     : https://prove2.me/theorems/cc441a31-0097-4a13-821e-d538955bfa97
-- title:
--   OAI.TuringRigidity.OrdinalArithmetic.internal_explicit_omega_threshold: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.OrdinalArithmetic.internal_explicit_omega_threshold` of [lean/OAI/Computability/DegreeRigidity/SetModels/RecursiveOmegaBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/RecursiveOmegaBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.OrdinalArithmetic`, with `open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding`):
--
--   ```lean
--   theorem internal_explicit_omega_threshold (M : ZFSet.{u}) (hM : Transitive M)
--       (hT : SourceT M) : ∃ θ : Ordinal.{u}, θ.toZFSet ∈ M ∧
--         ∀ a : Ordinal.{u}, OmegaPowerCertificates
--           (level (groundReals M) (θ+Ordinal.omega0 ^ (a+1))) a.toZFSet
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.OrdinalArithmetic.OmegaPowerCertificates` and `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.OrdinalCoding.cofinal_padded_code_certificates` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/RecursiveOmegaBound.lean (declaration OAI.TuringRigidity.OrdinalArithmetic.internal_explicit_omega_threshold)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem internal_explicit_omega_threshold (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : ∃ θ : Ordinal.{u}, θ.toZFSet ∈ M ∧
      ∀ a : Ordinal.{u}, OmegaPowerCertificates
        (level (groundReals M) (θ+Ordinal.omega0 ^ (a+1))) a.toZFSet := by
  sorry

end TuringRigidity.OrdinalArithmetic

end OAI
end
