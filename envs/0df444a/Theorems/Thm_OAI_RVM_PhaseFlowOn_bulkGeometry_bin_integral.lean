-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_bulkGeometry_bin_integral
-- name    : OAI.RVM.PhaseFlowOn.bulkGeometry_bin_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:16:12.067546+00:00
-- url     : https://prove2.me/theorems/e0d3ed68-efbb-4d25-a943-aee18c51e943
-- title:
--   OAI.RVM.PhaseFlowOn.bulkGeometry_bin_integral: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.bulkGeometry_bin_integral` of [lean/OAI/Analysis/VlasovMaxwell/Population/BulkSpatialUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/BulkSpatialUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.bulkGeometry_bin_integral {s : Solution} {T w : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
--       (Q : Set (Fin 4→ℕ)) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
--       (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈Icc a b,‖W t‖≤1)
--       {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
--       (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16) :
--       (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
--           (velocity (prefixFlow F.flow T zX z.1).2),
--         ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
--           (coneGeometryCutoffTangent s F.flow zX) W (Icc a b) (z,v)‖
--         ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
--         ENNReal.ofReal (650000*C)*representativeSpatialCost s F zX w k a b
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.coneBinMomentumSet`, `OAI.RVM.coneGeometryCutoffTangent`, `OAI.RVM.dyadicFactor`, `OAI.RVM.partialCutoffTriangle`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.prefixFlow`, `OAI.RVM.representativeClosedBin` and `OAI.RVM.representativeSpatialCost` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.bulk_geometry_uniform` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/BulkSpatialUniform.lean (declaration OAI.RVM.PhaseFlowOn.bulkGeometry_bin_integral)

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
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.bulkGeometry_bin_integral {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈Icc a b,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
        (coneGeometryCutoffTangent s F.flow zX) W (Icc a b) (z,v)‖
      ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal (650000*C)*representativeSpatialCost s F zX w k a b := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end
