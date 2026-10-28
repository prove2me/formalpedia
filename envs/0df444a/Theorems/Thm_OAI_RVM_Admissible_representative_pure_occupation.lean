-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_representative_pure_occupation
-- name    : OAI.RVM.Admissible.representative_pure_occupation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:10:25.253376+00:00
-- url     : https://prove2.me/theorems/5b7efb8b-1e01-4b9b-909e-1bdb8ac3b3b1
-- title:
--   OAI.RVM.Admissible.representative_pure_occupation: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.representative_pure_occupation` of [lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.representative_pure_occupation {d₀ : Datum} (hd₀ : Admissible d₀)
--       (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
--       ∀ᶠ P : ℝ in atTop,
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
--         zX∈tsupport d₀.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
--         cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
--         (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let B := representativeClosedBin T w k
--         coneOccupation F.flow zX T s.f
--           (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
--         ENNReal.ofReal ((1000000000*(max 1 T₀)^2)*pureOccupationEnvelope P 512 16384 M A
--           (sourceRepresentative (k 0)) w (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) I)*
--           ENNReal.ofReal (datumEnergyNumber d₀)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.closedBinEulerian`, `OAI.RVM.coneOccupation`, `OAI.RVM.datumEnergyNumber`, `OAI.RVM.pureOccupationEnvelope`, `OAI.RVM.representativeClosedBin` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.bulk_source_uniform`, `OAI.RVM.Admissible.unselected_small_source_uniform` and `OAI.RVM.Admissible.unselected_spatial_polynomial_cap` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean (declaration OAI.RVM.Admissible.representative_pure_occupation)

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

lemma Admissible.representative_pure_occupation {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d₀.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let B := representativeClosedBin T w k
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d₀.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal ((1000000000*(max 1 T₀)^2)*pureOccupationEnvelope P 512 16384 M A
        (sourceRepresentative (k 0)) w (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) I)*
        ENNReal.ofReal (datumEnergyNumber d₀) := by
  sorry

end RVM

end

end OAI
end
