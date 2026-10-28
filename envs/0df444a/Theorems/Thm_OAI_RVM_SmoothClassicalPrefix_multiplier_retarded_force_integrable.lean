-- Prove2me | Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_multiplier_retarded_force_integrable
-- name    : OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:20:22.956235+00:00
-- url     : https://prove2.me/theorems/607f1cc7-24fb-455a-a1f7-ae5d57b4ba5e
-- title:
--   OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_integrable (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_integrable` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma SmoothClassicalPrefix.multiplier_retarded_force_integrable {d : Datum} {s : Solution} {T : ℝ}
--       (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
--       (F : PhaseFlowOn s.E s.B T) (zX : Phase)
--       {W : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T)) :
--       IntegrableOn (fun t=>W t
--         (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
--           boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))
--         (Ioo (0:ℝ) T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.boundaryLorentzForce` and `OAI.RVM.datumBoundarySolution` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.cross` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direction_complete_count_cost_bound`, `OAI.RVM.Admissible.force_bulk_uniform` and `OAI_RVM_SmoothClassicalPrefix_direction_force_family_triangle` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean (declaration OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_integrable)

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

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

lemma SmoothClassicalPrefix.multiplier_retarded_force_integrable {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T)) :
    IntegrableOn (fun t=>W t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))
      (Ioo (0:ℝ) T) := by
  sorry

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end RVM

end

end OAI
end
