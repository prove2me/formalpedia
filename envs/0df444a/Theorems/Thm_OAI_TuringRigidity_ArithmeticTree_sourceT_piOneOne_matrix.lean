-- Prove2me | Theorems.Thm_OAI_TuringRigidity_ArithmeticTree_sourceT_piOneOne_matrix
-- name    : OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:31:21.39561+00:00
-- url     : https://prove2.me/theorems/16f01c97-bca9-46bc-8964-fba02fa588db
-- title:
--   OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix` of [lean/OAI/Computability/DegreeRigidity/Representation/SourceTTreeAbsoluteness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/SourceTTreeAbsoluteness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.ArithmeticTree`, with `open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel`, `open SetModelFunctions SetModelReals SetModelSyntax RelationCollapse`):
--
--   ```lean
--   theorem sourceT_piOneOne_matrix (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
--       {Q : Predicate} (hQ : Arith Q) (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) (v : ℕ) :
--       (∀ H ∈ reals M, Q (parameters A R H) v) ↔ ∀ H : Oracle, Q (parameters A R H) v
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.ArithmeticPersistence.parameters`, `OAI.TuringRigidity.SetModelReals.reals`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.UniformArithmetic.Arith` and `OAI.TuringRigidity.UniformArithmetic.Predicate` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/SourceTTreeAbsoluteness.lean (declaration OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelFunctions SetModelReals SetModelSyntax RelationCollapse
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

theorem sourceT_piOneOne_matrix (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {Q : Predicate} (hQ : Arith Q) (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) (v : ℕ) :
    (∀ H ∈ reals M, Q (parameters A R H) v) ↔ ∀ H : Oracle, Q (parameters A R H) v := by
  sorry

end
end TuringRigidity.ArithmeticTree

end OAI
end
