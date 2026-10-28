-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direct_source_shared_short_angles_expanded
-- name    : OAI.RVM.Admissible.direct_source_shared_short_angles_expanded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:05:35.431119+00:00
-- url     : https://prove2.me/theorems/6ac28c7d-b3f6-4082-a51e-db6d891e41e6
-- title:
--   OAI.RVM.Admissible.direct_source_shared_short_angles_expanded (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direct_source_shared_short_angles_expanded` of [lean/OAI/Analysis/VlasovMaxwell/Population/TransportRemainder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/TransportRemainder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory _root_.Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direct_source_shared_short_angles_expanded {d : Datum} (hd₀ : Admissible d) :
--       ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
--       ∀ (zX : Phase) (S : Set Phase) (np nφ : ℕ) (a b I w M A P : ℝ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<M → 0≤A → 0<P → 0<w →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--       ∀ (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ),
--         (∀i∈Sθ,cappedRepresentative nφ≤16384*cappedRepresentative i) →
--         (∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤131080*cappedRepresentative i ∧
--           512 ≤ cappedRepresentative j*sourceRepresentative np ∧ 32 ≤ cappedRepresentative j*w) →
--         let p := sourceRepresentative np
--         let φ := cappedRepresentative nφ
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let B := fun i j nr=>relativeRepresentativeClosedBin T w ![np,i,nφ,nr] j
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         let Kg := relativeCauchyConstant Cg E
--           (goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I nφ).toReal
--         let Kb := relativeCauchyConstant Cb E
--           (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
--         let D := dyadicBalanceConstant (1/2) (1/2)
--         let R₁ := 2*Real.sqrt 16384*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
--           (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
--         (∑i∈Sθ,∑j∈Sσ i,∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
--           ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B i j nr) z
--             ∂physicalBinMeasure V (B i j nr) (Icc a b) else 0) ≤
--         ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*
--           (Kg*(2*remainingGoodConstant 131080 16384 0*Real.sqrt φ+R₁*remainingGoodConstant 131080 16384 (1/2))+
--            Kb*(2*remainingMagneticConstant 131080 16384 0+R₁*remainingMagneticConstant 131080 16384 (1/2))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.dyadicBalanceConstant`, `OAI.RVM.goodFieldBudget`, `OAI.RVM.magneticFieldBudget`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalDirectSourceDensity`, `OAI.RVM.prefixFlow`, `OAI.RVM.relativeCauchyConstant`, `OAI.RVM.relativeRepresentativeClosedBin`, `OAI.RVM.remainingGoodConstant`, `OAI.RVM.remainingMagneticConstant`, `OAI.RVM.sourceRepresentative` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direct_remaining_source_short_uniform_expanded` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/TransportRemainder.lean (declaration OAI.RVM.Admissible.direct_source_shared_short_angles_expanded)

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

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

lemma Admissible.direct_source_shared_short_angles_expanded {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nφ : ℕ) (a b I w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<M → 0≤A → 0<P → 0<w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ),
      (∀i∈Sθ,cappedRepresentative nφ≤16384*cappedRepresentative i) →
      (∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤131080*cappedRepresentative i ∧
        512 ≤ cappedRepresentative j*sourceRepresentative np ∧ 32 ≤ cappedRepresentative j*w) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nφ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun i j nr=>relativeRepresentativeClosedBin T w ![np,i,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E
        (goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I nφ).toReal
      let Kb := relativeCauchyConstant Cb E
        (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
      let D := dyadicBalanceConstant (1/2) (1/2)
      let R₁ := 2*Real.sqrt 16384*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
      (∑i∈Sθ,∑j∈Sσ i,∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B i j nr) z
          ∂physicalBinMeasure V (B i j nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*
        (Kg*(2*remainingGoodConstant 131080 16384 0*Real.sqrt φ+R₁*remainingGoodConstant 131080 16384 (1/2))+
         Kb*(2*remainingMagneticConstant 131080 16384 0+R₁*remainingMagneticConstant 131080 16384 (1/2)))) := by
  sorry

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

end RVM

end

end OAI
end
