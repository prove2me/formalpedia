-- Prove2me | Theorems.Thm_OAI_RVM_integrated_electricMomentDensity_transport
-- name    : OAI.RVM.integrated_electricMomentDensity_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:26:16.779856+00:00
-- url     : https://prove2.me/theorems/ca418db1-c2e1-4dec-8522-6651e7027dcd
-- title:
--   OAI.RVM.integrated_electricMomentDensity_transport: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.integrated_electricMomentDensity_transport` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/ElectricConeBoundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ElectricConeBoundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma integrated_electricMomentDensity_transport {s : Solution}
--       (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
--       (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
--       (hc : CompactOnFiniteHorizons s) (hV : TransportFor s s.E s.B)
--       (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
--       (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
--       {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
--       (∫ z in ball (0:Vec) t, electricMomentDensity (fun p => rho (fun q => s.f (p.1,q)) p.2)
--         (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) =
--         (∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z) i) -
--         ∫ n : Sphere, t^2*dot n.1 (retardedElectricFlux s t x i (x+t • n.1)) ∂sphereMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.Sphere`, `OAI.RVM.TransportFor`, `OAI.RVM.electricMomentDensity`, `OAI.RVM.retardedElectricDensity`, `OAI.RVM.retardedElectricFlux` and `OAI.RVM.sphereMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.CompactOnFiniteHorizons`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.current`, `OAI.RVM.dot`, `OAI.RVM.fieldHalfSpace`, `OAI.RVM.particleHalfSpace` and `OAI.RVM.rho` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.mixed_electric_physical_representation` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ElectricConeBoundary.lean (declaration OAI.RVM.integrated_electricMomentDensity_transport)

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

lemma integrated_electricMomentDensity_transport {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s s.E s.B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) t, electricMomentDensity (fun p => rho (fun q => s.f (p.1,q)) p.2)
      (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) =
      (∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z) i) -
      ∫ n : Sphere, t^2*dot n.1 (retardedElectricFlux s t x i (x+t • n.1)) ∂sphereMeasure := by
  sorry

end RVM

end

end OAI
end
