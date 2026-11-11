-- Prove2me | Theorems.Thm_OAI_CurrentKS_Realization_isPoly_face_orbit
-- name    : OAI.CurrentKS.Realization.isPoly_face_orbit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:54:30.521264+00:00
-- url     : https://prove2.me/theorems/2dbce3cd-e2a5-41d8-bd5d-d62ebd59f05c
-- title:
--   OAI.CurrentKS.Realization.isPoly_face_orbit: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.Realization`, with `open CleanRoutine KS.W23 RationalSDP Hermitian`, `open scoped BigOperators MatrixOrder`):
--
--   ```lean
--   lemma isPoly_face_orbit (a : ι → FaceParams)
--       (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
--       IsPoly (fun s : ι×ℕ => L s.1) (fun s => (faceCode ((a s.1).orbit s.2)).length)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Realization.FaceParams` (definitions bundle `OAIQ241TT001` of this split); `OAI.CurrentKS.Realization.IsPoly`, `OAI.CurrentKS.Realization.faceCode`, `OAI.CurrentKS.Realization.FaceParams.GoodAtoms` and `OAI.CurrentKS.Realization.FaceParams.orbit` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.Realization.runsPoly_orbitStep` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT006

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalSDP Hermitian
open scoped BigOperators MatrixOrder

variable {ι : Type*} {L : ι → ℕ}
lemma isPoly_face_orbit (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    IsPoly (fun s : ι×ℕ => L s.1) (fun s => (faceCode ((a s.1).orbit s.2)).length) := by
  sorry
end CurrentKS.Realization

end OAI
end
