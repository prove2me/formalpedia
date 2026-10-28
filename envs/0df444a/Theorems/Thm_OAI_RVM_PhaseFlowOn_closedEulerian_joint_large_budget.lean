-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_joint_large_budget
-- name    : OAI.RVM.PhaseFlowOn.closedEulerian_joint_large_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:17:05.072307+00:00
-- url     : https://prove2.me/theorems/041c62be-0ef5-40f4-a16e-9b16f691c1a1
-- title:
--   OAI.RVM.PhaseFlowOn.closedEulerian_joint_large_budget: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.closedEulerian_joint_large_budget` of [lean/OAI/Analysis/VlasovMaxwell/Population/CentralOccupation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/CentralOccupation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.closedEulerian_joint_large_budget {s : Solution}
--       {T a b φ p len I : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
--       (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
--       (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
--       (ha : 0≤a) (hb : b≤T) (hlen : 0<len) (hlenI : len≤I) (hab : b-a≤I)
--       (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
--       (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hlarge : len<B.rmax)
--       (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2) :
--       coneOccupation F.flow zX T s.f
--         (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
--         ENNReal.ofReal (10240*B.rmax/p)*
--           (ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))+
--             ENNReal.ofReal (I/len)*jointEnergyBudget s F.flow zX T 4
--               (max 0 (a-2*I)) (min T (b+I)) I (np,nf))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.closedBinEulerian`, `OAI.RVM.coneOccupation`, `OAI.RVM.jointEnergyBudget` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.representative_large_shared_occupation` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/CentralOccupation.lean (declaration OAI.RVM.PhaseFlowOn.closedEulerian_joint_large_budget)

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

lemma PhaseFlowOn.closedEulerian_joint_large_budget {s : Solution}
    {T a b φ p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0≤a) (hb : b≤T) (hlen : 0<len) (hlenI : len≤I) (hab : b-a≤I)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hlarge : len<B.rmax)
    (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (10240*B.rmax/p)*
        (ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))+
          ENNReal.ofReal (I/len)*jointEnergyBudget s F.flow zX T 4
            (max 0 (a-2*I)) (min T (b+I)) I (np,nf)) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end
