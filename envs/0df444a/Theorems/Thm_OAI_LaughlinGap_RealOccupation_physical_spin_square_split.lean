-- Prove2me | Theorems.Thm_OAI_LaughlinGap_RealOccupation_physical_spin_square_split
-- name    : OAI.LaughlinGap.RealOccupation.physical_spin_square_split
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:52:35.531628+00:00
-- url     : https://prove2.me/theorems/0e8184fa-ff76-446d-b406-e0e9e6b09b18
-- title:
--   OAI.LaughlinGap.RealOccupation.physical_spin_square_split: intermediate lemma from OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinGap.RealOccupation.physical_spin_square_split` of [lean/OAI/Analysis/LaughlinGap/GlobalBoundCore.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/GlobalBoundCore.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinGap.RealOccupation`, with `open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator`, `open Averaging Spin Filter Topology`):
--
--   ```lean
--   lemma physical_spin_square_split {Q : ℕ} (hQ : 15 ≤ Q) :
--       physicalHamiltonian Q * physicalHamiltonian Q = physicalHamiltonian Q +
--         (threeRetained hQ + threeTailLift (by omega : 2 ≤ Q)) + fourTarget Q
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinGap.RealOccupation.FockMatrix` (definitions bundle `OAIQ030L013` of this split); `OAI.LaughlinGap.RealOccupation.fourTarget`, `OAI.LaughlinGap.RealOccupation.physicalHamiltonian`, `OAI.LaughlinGap.RealOccupation.threeRetained` and `OAI.LaughlinGap.RealOccupation.threeTailLift` (definitions bundle `OAIQ030L035` of this split).
--
--   **Used by.** The proof of `OAI.LaughlinGap.thm_main` of this split imports it.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/GlobalBoundCore.lean (declaration OAI.LaughlinGap.RealOccupation.physical_spin_square_split)

import Mathlib
import Definitions.Def_OAIQ030L035

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

lemma physical_spin_square_split {Q : ℕ} (hQ : 15 ≤ Q) :
    physicalHamiltonian Q * physicalHamiltonian Q = physicalHamiltonian Q +
      (threeRetained hQ + threeTailLift (by omega : 2 ≤ Q)) + fourTarget Q := by
  sorry

end LaughlinGap.RealOccupation

end

end OAI
end
