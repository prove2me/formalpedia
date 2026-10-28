-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direct_remaining_transport_angular_expanded
-- name    : OAI.RVM.Admissible.direct_remaining_transport_angular_expanded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:02:48.65272+00:00
-- url     : https://prove2.me/theorems/01d6e458-4f8a-4919-8e7a-b0517508315a
-- title:
--   OAI.RVM.Admissible.direct_remaining_transport_angular_expanded (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direct_remaining_transport_angular_expanded` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectExpandedTransportNear.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectExpandedTransportNear.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direct_remaining_transport_angular_expanded {d : Datum} (hd : Admissible d) :
--       ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
--       ∀ (zX : Phase) (S : Set Phase) (np : ℕ) (a b I w : ℝ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0≤a → b≤T → b-a≤I → 0<I →
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let B := fun nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
--         (∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
--           ∑'j : ℕ,∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nt nf j nr) z
--             ∂physicalBinMeasure V (B nt nf j nr) (Icc a b) else 0)≤
--         ENNReal.ofReal (C*I*max 1 T*sourceRepresentative np)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalDirectTransportDensity`, `OAI.RVM.prefixFlow`, `OAI.RVM.relativeRepresentativeClosedBin` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direct_transport_uniform` and `OAI.RVM.Admissible.unselected_label_uniform` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectExpandedTransportNear.lean (declaration OAI.RVM.Admissible.direct_remaining_transport_angular_expanded)

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

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_remaining_transport_angular_expanded {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤I → 0<I →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
        ∑'j : ℕ,∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nt nf j nr) z
          ∂physicalBinMeasure V (B nt nf j nr) (Icc a b) else 0)≤
      ENNReal.ofReal (C*I*max 1 T*sourceRepresentative np) := by
  sorry

end RVM

end

end OAI
end
