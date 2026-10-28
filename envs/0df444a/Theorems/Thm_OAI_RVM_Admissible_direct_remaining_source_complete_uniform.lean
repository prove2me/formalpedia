-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direct_remaining_source_complete_uniform
-- name    : OAI.RVM.Admissible.direct_remaining_source_complete_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:02:39.382216+00:00
-- url     : https://prove2.me/theorems/843fb1f9-dbc9-4732-8cbe-b5846e5db3b1
-- title:
--   OAI.RVM.Admissible.direct_remaining_source_complete_uniform: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direct_remaining_source_complete_uniform` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectExpandedAssemble.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectExpandedAssemble.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direct_remaining_source_complete_uniform {d : Datum} (hd : Admissible d) :
--       ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T →
--       ∀ (zX : Phase) (S : Set Phase) (a b I w M A P K : ℝ) (N : ℕ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
--         1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
--         I≤(w/P)^2 → 0≤K → (N:ℝ)≤K*Real.log (2+P) →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let B := fun np nf nt j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
--         let Sp := (Finset.range N).filter (fun np=>sourceRepresentative np≤128*P)
--         let Sf := (Finset.range N).filter (fun nf=>1/(32*w) ≤ cappedRepresentative nf)
--         let St := fun nf=>(Finset.range N).filter (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt)
--         let Ss := fun nt=>(Finset.range N).filter (fun j=>cappedRepresentative j≤131080*cappedRepresentative nt)
--         (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,∑'nr : ℕ,
--           ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
--             ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b))≤
--         ENNReal.ofReal (C*(1+K^4)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalDirectSourceDensity`, `OAI.RVM.prefixFlow`, `OAI.RVM.relativeRepresentativeClosedBin` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direct_source_absolute_uniform` and `OAI.RVM.Admissible.unselected_source_uniform` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectExpandedAssemble.lean (declaration OAI.RVM.Admissible.direct_remaining_source_complete_uniform)

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

lemma Admissible.direct_remaining_source_complete_uniform {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w M A P K : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      I≤(w/P)^2 → 0≤K → (N:ℝ)≤K*Real.log (2+P) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nf nt j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      let Sp := (Finset.range N).filter (fun np=>sourceRepresentative np≤128*P)
      let Sf := (Finset.range N).filter (fun nf=>1/(32*w) ≤ cappedRepresentative nf)
      let St := fun nf=>(Finset.range N).filter (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt)
      let Ss := fun nt=>(Finset.range N).filter (fun j=>cappedRepresentative j≤131080*cappedRepresentative nt)
      (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,∑'nr : ℕ,
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
          ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b))≤
      ENNReal.ofReal (C*(1+K^4)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end
