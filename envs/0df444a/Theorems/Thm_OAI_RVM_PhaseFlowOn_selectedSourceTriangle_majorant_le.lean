-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_selectedSourceTriangle_majorant_le
-- name    : OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:55.412915+00:00
-- url     : https://prove2.me/theorems/3a9953cd-b169-4104-98b3-8e06df0a51e8
-- title:
--   OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/ConeForceSplit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ConeForceSplit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.selectedSourceTriangle_majorant_le {s : Solution} {T w : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
--       {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
--       (B : ClosedConeBin) {z : ConeCoordinate}
--       (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
--       (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
--         ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX)
--           (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
--         ENNReal.ofReal 64*physicalSourceMajorantDensity s (fun t=>(prefixFlow F.flow T zX t).1)
--           (fun t=>(prefixFlow F.flow T zX t).2) B z
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.coneBinMomentumSet`, `OAI.RVM.physicalBinBase`, `OAI.RVM.physicalSourceMajorantDensity`, `OAI.RVM.prefixAngularMultiplier`, `OAI.RVM.prefixFlow`, `OAI.RVM.selectedConeTriangle` and `OAI.RVM.sourceOnlyConeKernel` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.PhaseFlowOn.unselected_source_label_physical_sum` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ConeForceSplit.lean (declaration OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le)

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

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.selectedSourceTriangle_majorant_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      ENNReal.ofReal 64*physicalSourceMajorantDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z := by
  sorry

end RVM

end

end OAI
end
