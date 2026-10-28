-- Prove2me | Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_representativeJointEnergy_sum
-- name    : OAI.RVM.SmoothClassicalPrefix.representativeJointEnergy_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:21:19.059187+00:00
-- url     : https://prove2.me/theorems/9888f9bc-cdc6-4ed9-acb6-e8a9bd689ccf
-- title:
--   OAI.RVM.SmoothClassicalPrefix.representativeJointEnergy_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.SmoothClassicalPrefix.representativeJointEnergy_sum` of [lean/OAI/Analysis/VlasovMaxwell/Population/SharedOccupation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SharedOccupation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma SmoothClassicalPrefix.representativeJointEnergy_sum {d : Datum} {s : Solution} {T : ℝ}
--       (hs : SmoothClassicalPrefix d s T) (hd : Admissible d) (F : PhaseFlowOn s.E s.B T) (zX : Phase)
--       {a b I : ℝ} (hI : 0<I) (hab : b-a≤I) :
--       Summable (representativeJointEnergy s F zX a b I) ∧
--         (∑'n,representativeJointEnergy s F zX a b I n)≤3468*datumEnergyNumber d ∧
--       ∀n,jointEnergyBudget s F.flow zX T 4 (max 0 (a-2*I)) (min T (b+I)) I n=
--         ENNReal.ofReal (representativeJointEnergy s F zX a b I n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.datumEnergyNumber`, `OAI.RVM.jointEnergyBudget` and `OAI.RVM.representativeJointEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase` and `OAI.RVM.Solution` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.central_regular_uniform`, `OAI.RVM.Admissible.good_structural_uniform`, `OAI.RVM.Admissible.magnetic_small_uniform`, `OAI.RVM.Admissible.representative_large_shared_occupation`, `OAI.RVM.Admissible.representative_shared_occupation`, `OAI.RVM.Admissible.small_good_uniform`, `OAI.RVM.Admissible.small_transport_regular_uniform` and `OAI.RVM.Admissible.spatial_transition_regular_uniform` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SharedOccupation.lean (declaration OAI.RVM.SmoothClassicalPrefix.representativeJointEnergy_sum)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.representativeJointEnergy_sum {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hd : Admissible d) (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {a b I : ℝ} (hI : 0<I) (hab : b-a≤I) :
    Summable (representativeJointEnergy s F zX a b I) ∧
      (∑'n,representativeJointEnergy s F zX a b I n)≤3468*datumEnergyNumber d ∧
    ∀n,jointEnergyBudget s F.flow zX T 4 (max 0 (a-2*I)) (min T (b+I)) I n=
      ENNReal.ofReal (representativeJointEnergy s F zX a b I n) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
