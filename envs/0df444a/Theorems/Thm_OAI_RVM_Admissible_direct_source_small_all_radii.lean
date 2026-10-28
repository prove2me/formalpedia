-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direct_source_small_all_radii
-- name    : OAI.RVM.Admissible.direct_source_small_all_radii
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:05:22.070263+00:00
-- url     : https://prove2.me/theorems/bd2f0d33-9725-4989-9434-786840f83670
-- title:
--   OAI.RVM.Admissible.direct_source_small_all_radii: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direct_source_small_all_radii` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/GeneralDirectRadial.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/GeneralDirectRadial.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direct_source_small_all_radii {d : Datum} (hd₀ : Admissible d) :
--       ∃ C : ℝ, 0≤C ∧
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
--       ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
--         0 < M → 0 ≤ A → 1 ≤ P → 1 ≤ Real.log (2+P) → 1 ≤ w → w≤P →
--         sourceRepresentative np≤128*P →
--         cappedRepresentative nθ ≤ cappedRepresentative nφ →
--         cappedRepresentative nφ≤8*cappedRepresentative j →
--         1 ≤ sourceRepresentative np*cappedRepresentative nθ →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
--           ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
--         ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalDirectSourceDensity`, `OAI.RVM.prefixFlow`, `OAI.RVM.relativeRepresentativeClosedBin`, `OAI.RVM.sourceRepresentative` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI_RVM_Admissible_direct_source_all_radii` and `OAI.RVM.Admissible.direct_source_physical_log_bound` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/GeneralDirectRadial.lean (declaration OAI.RVM.Admissible.direct_source_small_all_radii)

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

lemma Admissible.direct_source_small_all_radii {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0≤C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 1 ≤ P → 1 ≤ Real.log (2+P) → 1 ≤ w → w≤P →
      sourceRepresentative np≤128*P →
      cappedRepresentative nθ ≤ cappedRepresentative nφ →
      cappedRepresentative nφ≤8*cappedRepresentative j →
      1 ≤ sourceRepresentative np*cappedRepresentative nθ →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
