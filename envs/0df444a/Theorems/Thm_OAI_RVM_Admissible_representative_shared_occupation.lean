-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_representative_shared_occupation
-- name    : OAI.RVM.Admissible.representative_shared_occupation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:11:21.317523+00:00
-- url     : https://prove2.me/theorems/c5137517-e347-4255-9920-31c386f655e0
-- title:
--   OAI.RVM.Admissible.representative_shared_occupation: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.representative_shared_occupation` of [lean/OAI/Analysis/VlasovMaxwell/Population/SharedOccupation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SharedOccupation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.representative_shared_occupation {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
--       ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
--         zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
--         cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
--         512/min (sourceRepresentative (k 0)) w < cappedRepresentative (k 2) →
--         (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let B := representativeClosedBin T w k
--         coneOccupation F.flow zX T s.f
--           (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
--         ENNReal.ofReal (C*cappedRepresentative (k 3)/sourceRepresentative (k 0)*
--           (representativeSharedRadius s F zX P M A w a b I (k 0,k 2))^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.closedBinEulerian`, `OAI.RVM.coneOccupation`, `OAI.RVM.representativeClosedBin`, `OAI.RVM.representativeSharedRadius` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.representative_regular_central_shared` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SharedOccupation.lean (declaration OAI.RVM.Admissible.representative_shared_occupation)

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

lemma Admissible.representative_shared_occupation {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      512/min (sourceRepresentative (k 0)) w < cappedRepresentative (k 2) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let B := representativeClosedBin T w k
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (C*cappedRepresentative (k 3)/sourceRepresentative (k 0)*
        (representativeSharedRadius s F zX P M A w a b I (k 0,k 2))^2) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
