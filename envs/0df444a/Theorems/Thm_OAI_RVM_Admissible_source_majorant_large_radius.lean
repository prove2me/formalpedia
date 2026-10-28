-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_source_majorant_large_radius
-- name    : OAI.RVM.Admissible.source_majorant_large_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:12:13.529279+00:00
-- url     : https://prove2.me/theorems/f659231e-2f9c-475c-b403-7fc588a8fb50
-- title:
--   OAI.RVM.Admissible.source_majorant_large_radius: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.source_majorant_large_radius` of [lean/OAI/Analysis/VlasovMaxwell/Population/MajorantRelativeDensityTimeFar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/MajorantRelativeDensityTimeFar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.source_majorant_large_radius {d : Datum} (hd₀ : Admissible d) :
--       ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
--       ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
--         (a b I w : ℝ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
--         I ≤ max 1 T*cappedRepresentative (k 3) →
--         let p := sourceRepresentative (k 0)
--         let θ := cappedRepresentative (k 1)
--         let φ := cappedRepresentative (k 2)
--         let σ := cappedRepresentative j
--         let r := max 1 T*cappedRepresentative (k 3)
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let B := relativeRepresentativeClosedBin T w k j
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         let ν := min θ σ
--         let Kg := majorant_relativeCauchyConstant Cg E (20*E)
--         let Kb := majorant_relativeCauchyConstant Cb E (120*E)
--         (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z
--           ∂physicalBinMeasure V B (Icc a b)) ≤
--         ENNReal.ofReal (Kg*min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
--           ((Real.sqrt I*ν/θ^2)/Real.sqrt r)+
--         Kb*Real.sqrt I*min (r*p^2*ν^2*φ) (Real.sqrt p*ν/(θ*Real.sqrt r)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.majorant_relativeCauchyConstant`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalSourceMajorantDensity`, `OAI.RVM.prefixFlow`, `OAI.RVM.relativeRepresentativeClosedBin`, `OAI.RVM.sourceRepresentative` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.source_majorant_remaining_large_sum` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/MajorantRelativeDensityTimeFar.lean (declaration OAI.RVM.Admissible.source_majorant_large_radius)

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

lemma Admissible.source_majorant_large_radius {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
      (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      I ≤ max 1 T*cappedRepresentative (k 3) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let ν := min θ σ
      let Kg := majorant_relativeCauchyConstant Cg E (20*E)
      let Kb := majorant_relativeCauchyConstant Cb E (120*E)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (Kg*min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
        ((Real.sqrt I*ν/θ^2)/Real.sqrt r)+
      Kb*Real.sqrt I*min (r*p^2*ν^2*φ) (Real.sqrt p*ν/(θ*Real.sqrt r))) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
