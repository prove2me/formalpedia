-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_tail_sum
-- name    : OAI.Laughlin.Fock.physical_threeBody_tail_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:31:40.284927+00:00
-- url     : https://prove2.me/theorems/37ed3ebf-7cd5-4442-bf32-09fc29e88429
-- title:
--   OAI.Laughlin.Fock.physical_threeBody_tail_sum: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.physical_threeBody_tail_sum` of [lean/OAI/Analysis/Laughlin/ThreeBody/FockTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/FockTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem physical_threeBody_tail_sum (Q : ℕ) (hQ : 4 ≤ Q) (x : Space Q) :
--       -(deltaFormula Q * sourceFockEnergy Q x) ≤
--         ∑ z : Fin (Q+1), if 16 ≤ z.val then gramEigenvalueFormula Q z.val *
--           (contractionForm Q (sourceThreeEnd Q)
--             ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.Space`, `OAI.Laughlin.Fock.contractionForm`, `OAI.Laughlin.Spin.Orbital`, `OAI.Laughlin.Spin.PairOrbitalIndex` and `OAI.Laughlin.Spin.threeSpinProjector` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.deltaFormula` and `OAI.Laughlin.gramEigenvalueFormula` (definitions bundle `OAIQ047L001` of this split); `OAI.Laughlin.Fock.sourceFockEnergy` and `OAI.Laughlin.Fock.sourceThreeEnd` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proofs of `OAI_Laughlin_Fock_physical_fock_square_uniform` and `OAI.Laughlin.Fock.physical_threeBody_budget_eventually` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/FockTail.lean (declaration OAI.Laughlin.Fock.physical_threeBody_tail_sum)

import Mathlib
import Definitions.Def_OAIQ047L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physical_threeBody_tail_sum (Q : ℕ) (hQ : 4 ≤ Q) (x : Space Q) :
    -(deltaFormula Q * sourceFockEnergy Q x) ≤
      ∑ z : Fin (Q+1), if 16 ≤ z.val then gramEigenvalueFormula Q z.val *
        (contractionForm Q (sourceThreeEnd Q)
          ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re else 0 := by
  sorry

end Laughlin.Fock

end OAI
end
