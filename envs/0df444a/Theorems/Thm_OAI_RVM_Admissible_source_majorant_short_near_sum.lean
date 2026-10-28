-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_source_majorant_short_near_sum
-- name    : OAI.RVM.Admissible.source_majorant_short_near_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:13:00.660848+00:00
-- url     : https://prove2.me/theorems/0de1656a-0cde-4c0b-8b22-dd0fe3047a56
-- title:
--   OAI.RVM.Admissible.source_majorant_short_near_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.source_majorant_short_near_sum` of [lean/OAI/Analysis/VlasovMaxwell/Population/MajorantRelativeDensityTimeFar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/MajorantRelativeDensityTimeFar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.source_majorant_short_near_sum {d : Datum} (hd₀ : Admissible d) :
--       ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
--       ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w : ℝ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
--         let p := sourceRepresentative np
--         let θ := cappedRepresentative nθ
--         let φ := cappedRepresentative nφ
--         let σ := cappedRepresentative j
--         let ν := min θ σ
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         let Kg := majorant_relativeCauchyConstant Cg E (20*E)
--         let Kb := majorant_relativeCauchyConstant Cb E (120*E)
--         (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
--           ∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V (B nr) z
--             ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
--         ENNReal.ofReal ((Kg*(I*p^2*ν^2*φ^2/θ^2)+Kb*(I*p^2*ν^2*φ))*
--           (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt I)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.majorant_relativeCauchyConstant`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalSourceMajorantDensity`, `OAI.RVM.prefixFlow`, `OAI.RVM.relativeRepresentativeClosedBin`, `OAI.RVM.sourceRepresentative` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.source_majorant_remaining_all_radii` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/MajorantRelativeDensityTimeFar.lean (declaration OAI.RVM.Admissible.source_majorant_short_near_sum)

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

lemma Admissible.source_majorant_short_near_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      let p := sourceRepresentative np
      let θ := cappedRepresentative nθ
      let φ := cappedRepresentative nφ
      let σ := cappedRepresentative j
      let ν := min θ σ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := majorant_relativeCauchyConstant Cg E (20*E)
      let Kb := majorant_relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((Kg*(I*p^2*ν^2*φ^2/θ^2)+Kb*(I*p^2*ν^2*φ))*
        (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt I) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
