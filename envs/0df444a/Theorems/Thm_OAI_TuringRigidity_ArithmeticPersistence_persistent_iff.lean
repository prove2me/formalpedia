-- Prove2me | Theorems.Thm_OAI_TuringRigidity_ArithmeticPersistence_persistent_iff
-- name    : OAI.TuringRigidity.ArithmeticPersistence.persistent_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:33:11.080333+00:00
-- url     : https://prove2.me/theorems/90a710b6-7d18-461f-bd97-26a66cbdb662
-- title:
--   OAI.TuringRigidity.ArithmeticPersistence.persistent_iff: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.ArithmeticPersistence.persistent_iff` of [lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticPersistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticPersistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.ArithmeticPersistence`, with `open Encodable EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic`, `open PersistentRestrictions PersistentPresentation PersistentCountability`, `open NumericalAutomorphism NumericalIdeal NumericalExtension`):
--
--   ```lean
--   theorem persistent_iff {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
--       (ρ : I ≃o I) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
--       (hR : ∀ v, R v = true ↔ Graph ρ hA v) :
--       Persistent I ρ ↔ Criterion A R
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.ArithmeticPersistence.Criterion`, `OAI.TuringRigidity.OracleJump.jump` and `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentPresentation.Graph`, `OAI.TuringRigidity.PersistentPresentation.Presented` and `OAI.TuringRigidity.PersistentRestrictions.Persistent` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticPersistence.lean (declaration OAI.TuringRigidity.ArithmeticPersistence.persistent_iff)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A003
import Definitions.Def_OAIQ064A004

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticPersistence
open Encodable EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic
open PersistentRestrictions PersistentPresentation PersistentCountability
open NumericalAutomorphism NumericalIdeal NumericalExtension
noncomputable section

theorem persistent_iff {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (ρ : I ≃o I) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ Graph ρ hA v) :
    Persistent I ρ ↔ Criterion A R := by
  sorry

end
end TuringRigidity.ArithmeticPersistence

end OAI
end
