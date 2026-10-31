-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_rowSum_adjoint
-- name    : OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:08:18.729854+00:00
-- url     : https://prove2.me/theorems/a2265f13-2d47-457a-8de5-1a1d5f7eb7af
-- title:
--   OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint` of [lean/OAI/Analysis/NuclearUltrapower/CuntzIntertwining.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzIntertwining.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.CuntzAveraging`, with `open Filter`, `open scoped TensorProduct InnerProductSpace Topology`, `open CuntzModel CuntzWords CuntzUniversal`):
--
--   ```lean
--   theorem rowSum_adjoint (N : ℕ) (i : Fin 2) :
--       (rowSum R N).comp (star (R (generator i))) - (star (left i)).comp (rowSum R N) =
--         (star (left i)).comp ((row R N)-(row R 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.CuntzAveraging.Target`, `OAI.NuclearUltrapower.CuntzAveraging.left`, `OAI.NuclearUltrapower.CuntzModel.Index` and `OAI.NuclearUltrapower.CuntzModel.Space` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.CuntzAveraging.row`, `OAI.NuclearUltrapower.CuntzAveraging.rowSum`, `OAI.NuclearUltrapower.CuntzUniversal.Algebra`, `OAI.NuclearUltrapower.CuntzUniversal.generator` and `OAI.NuclearUltrapower.CuntzUniversal.instCStarAlgebraAlgebra` (definitions bundle `OAIQ019N039` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.CuntzAveraging.defect_adjoint_bound` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzIntertwining.lean (declaration OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint)

import Mathlib
import Definitions.Def_OAIQ019N039

section

attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

theorem rowSum_adjoint (N : ℕ) (i : Fin 2) :
    (rowSum R N).comp (star (R (generator i))) - (star (left i)).comp (rowSum R N) =
      (star (left i)).comp ((row R N)-(row R 0)) := by
  sorry

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end
