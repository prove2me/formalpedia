-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_representative_regular_central_shared
-- name    : OAI.RVM.Admissible.representative_regular_central_shared
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:10:59.178793+00:00
-- url     : https://prove2.me/theorems/e2322b0b-bb42-496a-b898-89c8782e776e
-- title:
--   OAI.RVM.Admissible.representative_regular_central_shared: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.representative_regular_central_shared` of [lean/OAI/Analysis/VlasovMaxwell/Population/CentralOccupation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/CentralOccupation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.representative_regular_central_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
--       ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
--         zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
--         cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
--         (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let p := sourceRepresentative (k 0)
--         let θ := cappedRepresentative (k 1)
--         let φ := cappedRepresentative (k 2)
--         let h := cappedRepresentative (k 3)
--         let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
--         representativeRegularCentralCost s F zX P M A I w k a b≤
--           ENNReal.ofReal (C*min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.representativeRegularCentralCost`, `OAI.RVM.representativeSharedRadius` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.central_regular_uniform`, `OAI.RVM.Admissible.good_regular_double_sum`, `OAI.RVM.Admissible.representative_regular_good_structural_double_sum`, `OAI.RVM.Admissible.representative_regular_short_magnetic`, `OAI.RVM.Admissible.small_transport_regular_uniform` and `OAI.RVM.Admissible.spatial_transition_regular_uniform` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/CentralOccupation.lean (declaration OAI.RVM.Admissible.representative_regular_central_shared)

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

lemma Admissible.representative_regular_central_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeRegularCentralCost s F zX P M A I w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end
