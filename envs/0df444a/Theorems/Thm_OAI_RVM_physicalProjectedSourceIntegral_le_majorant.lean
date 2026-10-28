-- Prove2me | Theorems.Thm_OAI_RVM_physicalProjectedSourceIntegral_le_majorant
-- name    : OAI.RVM.physicalProjectedSourceIntegral_le_majorant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:27:18.620085+00:00
-- url     : https://prove2.me/theorems/380d6aa4-94d9-497a-924e-4b4e1b63f909
-- title:
--   OAI.RVM.physicalProjectedSourceIntegral_le_majorant: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.physicalProjectedSourceIntegral_le_majorant` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceMajorant.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceMajorant.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma physicalProjectedSourceIntegral_le_majorant {s : Solution} {T w c : ℝ}
--       (hs : EnergyPrefix s T) {X V : ℝ→Vec} (hV : Measurable V)
--       (C : ClosedConeBin) (Q : Set (Fin 4→ℕ)) {J : Set ℝ}
--       (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
--       (hc : 0 ≤ c) (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ c)
--       (hw : 0<w) (hW : ∀t∈J,w/16≤‖V t‖) (hr : 0<C.rmin)
--       (hsmall : C.dmax≤C.Dmin) :
--       (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V C T w Q z
--         ∂physicalBinMeasure V C J) ≤
--       ENNReal.ofReal (64+5880000*c)*
--         ∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V C z
--           ∂physicalBinMeasure V C J
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.Sphere`, `OAI.RVM.dyadicFactor`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalProjectedSourceDensity` and `OAI.RVM.physicalSourceMajorantDensity` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.projected_source_structural_edge_log_sum` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceMajorant.lean (declaration OAI.RVM.physicalProjectedSourceIntegral_le_majorant)

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

lemma physicalProjectedSourceIntegral_le_majorant {s : Solution} {T w c : ℝ}
    (hs : EnergyPrefix s T) {X V : ℝ→Vec} (hV : Measurable V)
    (C : ClosedConeBin) (Q : Set (Fin 4→ℕ)) {J : Set ℝ}
    (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hc : 0 ≤ c) (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ c)
    (hw : 0<w) (hW : ∀t∈J,w/16≤‖V t‖) (hr : 0<C.rmin)
    (hsmall : C.dmax≤C.Dmin) :
    (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V C T w Q z
      ∂physicalBinMeasure V C J) ≤
    ENNReal.ofReal (64+5880000*c)*
      ∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V C z
        ∂physicalBinMeasure V C J := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
