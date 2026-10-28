-- Prove2me | Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_physical_vectors
-- name    : OAI.RVM.SmoothClassicalPrefix.physical_vectors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:21:22.412002+00:00
-- url     : https://prove2.me/theorems/52249d9f-a281-4716-a5b0-46bcd9d70360
-- title:
--   OAI.RVM.SmoothClassicalPrefix.physical_vectors: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.SmoothClassicalPrefix.physical_vectors` of [lean/OAI/Analysis/VlasovMaxwell/Regularity/PhysicalC0.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/PhysicalC0.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma SmoothClassicalPrefix.physical_vectors {d : Datum} {s : Solution} {H t : ℝ}
--       (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (hHt : t<H) (x : Vec) :
--       (s.E (t,x)=electricBoundaryField (datumBoundarySolution d) t x+
--         (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z)) ∧
--       (s.B (t,x)=magneticBoundaryField (datumBoundarySolution d) t x+
--         (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) ∧
--       IntegrableOn (fun z => retardedElectricDensity s t x (x+z)) (ball (0:Vec) t) ∧
--       IntegrableOn (fun z => retardedMagneticDensity s t x (x+z)) (ball (0:Vec) t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.datumBoundarySolution`, `OAI.RVM.electricBoundaryField`, `OAI.RVM.magneticBoundaryField`, `OAI.RVM.retardedElectricDensity` and `OAI.RVM.retardedMagneticDensity` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.physical_fields_volterra` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/PhysicalC0.lean (declaration OAI.RVM.SmoothClassicalPrefix.physical_vectors)

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
open scoped Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.physical_vectors {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (hHt : t<H) (x : Vec) :
    (s.E (t,x)=electricBoundaryField (datumBoundarySolution d) t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z)) ∧
    (s.B (t,x)=magneticBoundaryField (datumBoundarySolution d) t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) ∧
    IntegrableOn (fun z => retardedElectricDensity s t x (x+z)) (ball (0:Vec) t) ∧
    IntegrableOn (fun z => retardedMagneticDensity s t x (x+z)) (ball (0:Vec) t) := by
  sorry

end RVM
end

end OAI
end
