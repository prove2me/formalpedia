-- Prove2me | Theorems.Thm_OAI_CurrentKS_Realization_runsPoly_orbitStep
-- name    : OAI.CurrentKS.Realization.runsPoly_orbitStep
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:17:07.081335+00:00
-- url     : https://prove2.me/theorems/56a035ad-39db-46ae-8198-dc78672c9411
-- title:
--   OAI.CurrentKS.Realization.runsPoly_orbitStep: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.Realization`, with `open CleanRoutine KS.W23`):
--
--   ```lean
--   lemma runsPoly_orbitStep (a : ι → FaceParams)
--       (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
--       RunsPoly (fun s : ι×ℕ => L s.1) faceNext (fun s => (a s.1).orbit s.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Realization.FaceParams` (definitions bundle `OAIQ241TT001` of this split); `OAI.CurrentKS.Realization.IsPoly`, `OAI.CurrentKS.Realization.RunsPoly`, `OAI.CurrentKS.Realization.faceCode`, `OAI.CurrentKS.Realization.FaceParams.GoodAtoms`, `OAI.CurrentKS.Realization.FaceParams.next` and `OAI.CurrentKS.Realization.FaceParams.orbit` (definitions bundle `OAIQ241TT006` of this split); `OAI.CurrentKS.Realization.faceNext` (definitions bundle `OAIQ241TT014` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.Realization.runsPoly_normalizedRun` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT014

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_orbitStep (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    RunsPoly (fun s : ι×ℕ => L s.1) faceNext (fun s => (a s.1).orbit s.2) := by
  sorry

end CurrentKS.Realization

end

end OAI
end
