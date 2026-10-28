-- Prove2me | Theorems.Thm_OAI_TuringRigidity_ArithmeticTree_setGenericallyPersistent_iff
-- name    : OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:34:14.942356+00:00
-- url     : https://prove2.me/theorems/59ef3bf5-006e-4dfd-a545-6c75f22c8961
-- title:
--   OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff` of [lean/OAI/Computability/DegreeRigidity/Representation/NativeGenericWitness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/NativeGenericWitness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.ArithmeticTree`, with `open BoundedSetTheory TransitiveNameModel SetDegreeDecoding PersistentRestrictions`, `open CountableForcing AtomicForcing`):
--
--   ```lean
--   theorem setGenericallyPersistent_iff (M : ZFSet.{u}) [Countable (Conditions M)]
--       (hM : Transitive M) (hT : SourceT M) (I : CountableIdeal)
--       (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
--       (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
--       SetGenericallyPersistent M I ρ ↔ Persistent I ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.ArithmeticTree.SetGenericallyPersistent`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.SetDegreeDecoding.idealSet`, `OAI.TuringRigidity.TransitiveNameModel.Conditions` and `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentRestrictions.Persistent` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.Degree` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names` and `OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/NativeGenericWitness.lean (declaration OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003
import Definitions.Def_OAIQ064A004

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open BoundedSetTheory TransitiveNameModel SetDegreeDecoding PersistentRestrictions
open CountableForcing AtomicForcing
universe u

theorem setGenericallyPersistent_iff (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (I : CountableIdeal)
    (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    SetGenericallyPersistent M I ρ ↔ Persistent I ρ := by
  sorry

end TuringRigidity.ArithmeticTree

end OAI
end
