-- Prove2me | Theorems.Thm_OAI_SourceBurnside_SourceMachine_MachineHierarchy_matrixNilKernel
-- name    : OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:16:09.012139+00:00
-- url     : https://prove2.me/theorems/b43f36a2-f087-4572-9f34-f0dfc6385f37
-- title:
--   OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel: intermediate lemma from OpenAI, An infinite finitely presented periodic group
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel` of [lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Steinberg/CoefficientQuotients.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Steinberg/CoefficientQuotients.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SourceBurnside.SourceMachine.MachineHierarchy`, with `open Classical FiniteTable`):
--
--   ```lean
--   theorem matrixNilKernel (hDbig : 10*(10000+1)*(10+1)<D) :
--       MatrixNilKernel (A.augmentation hh (ZMod 2)).toRingHom
--   ```
--
--   **Definitions.** The statement is written with `OAI.SourceBurnside.FiniteTable.Codec.Raw` (definitions bundle `OAIQ18Pg000` of this split); `OAI.SourceBurnside.WordAlgebra.Polynomial`, `OAI.SourceBurnside.WordAlgebra.Word` and `OAI.SourceBurnside.WordAlgebra.Table.ideal` (definitions bundle `OAIQ18Pg001` of this split); `OAI.SourceBurnside.MatrixNilKernel` (definitions bundle `OAIQ18Pg002` of this split); `OAI.SourceBurnside.SourceMachine.MachineHierarchy` (definitions bundle `OAIQ18Pg005` of this split); `OAI.SourceBurnside.SourceMachine.MachineHierarchy.Algebra`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.augmentation` and `OAI.SourceBurnside.SourceMachine.MachineHierarchy.table` (definitions bundle `OAIQ18Pg009` of this split).
--
--   **Used by.** The proofs of `OAI.SourceBurnside.ConcreteSource.matrix_nil_kernel` and `OAI.SourceBurnside.ConcreteSource.matrix_periodic` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Steinberg/CoefficientQuotients.lean (declaration OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel)

import Mathlib
import Definitions.Def_OAIQ18Pg009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h)

theorem matrixNilKernel (hDbig : 10*(10000+1)*(10+1)<D) :
    MatrixNilKernel (A.augmentation hh (ZMod 2)).toRingHom := by
  sorry

end
end SourceBurnside.SourceMachine.MachineHierarchy

end

end OAI
end
