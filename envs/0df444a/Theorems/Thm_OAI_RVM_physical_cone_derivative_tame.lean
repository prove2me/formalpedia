-- Prove2me | Theorems.Thm_OAI_RVM_physical_cone_derivative_tame
-- name    : OAI.RVM.physical_cone_derivative_tame
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:28:07.050994+00:00
-- url     : https://prove2.me/theorems/f57de96b-64d8-4310-8170-b5331a87a016
-- title:
--   OAI.RVM.physical_cone_derivative_tame: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.physical_cone_derivative_tame` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/ConeRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ConeRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma physical_cone_derivative_tame (k : ℕ) (hk : 1≤k) (P A : ℝ) (hA : 1≤A) :
--       ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution), ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s.E → ContDiff ℝ ∞ s.B →
--         CompactOnFiniteHorizons s → ∀ T : ℝ, T≤1 →
--         (∀ u∈Icc (0:ℝ) T, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0) →
--         ParticleJetBound k T A s.f → SpatialJetBound k T A s.E s.B →
--         ∀ H : ℝ → ℝ, Continuous H → (∀ u∈Icc (0:ℝ) T, 0≤H u) →
--         (∀ u∈Icc (0:ℝ) T, ∀ z, ‖iteratedFDeriv ℝ (k+1) (fun w => s.f (u,w)) z‖≤H u) →
--         (∀ u∈Icc (0:ℝ) T, ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => s.E (u,y)) x‖≤H u ∧
--           ‖iteratedFDeriv ℝ (k+1) (fun y => s.B (u,y)) x‖≤H u) →
--         ∀ t∈Icc (0:ℝ) T, ∀ x,
--           ‖iteratedFDeriv ℝ (k+1) (fun y => ∫ z in ball (0:Vec) t,
--             retardedElectricDensity s t y (y+z)) x‖ ≤ C*(∫ u in Icc (0:ℝ) t, 1+H u) ∧
--           ‖iteratedFDeriv ℝ (k+1) (fun y => ∫ z in ball (0:Vec) t,
--             retardedMagneticDensity s t y (y+z)) x‖ ≤ C*(∫ u in Icc (0:ℝ) t, 1+H u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ParticleJetBound`, `OAI.RVM.SpatialJetBound`, `OAI.RVM.retardedElectricDensity` and `OAI.RVM.retardedMagneticDensity` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.CompactOnFiniteHorizons`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.uniform_picard_sequence_jets` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ConeRegularity.lean (declaration OAI.RVM.physical_cone_derivative_tame)

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

lemma physical_cone_derivative_tame (k : ℕ) (hk : 1≤k) (P A : ℝ) (hA : 1≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution), ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s.E → ContDiff ℝ ∞ s.B →
      CompactOnFiniteHorizons s → ∀ T : ℝ, T≤1 →
      (∀ u∈Icc (0:ℝ) T, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0) →
      ParticleJetBound k T A s.f → SpatialJetBound k T A s.E s.B →
      ∀ H : ℝ → ℝ, Continuous H → (∀ u∈Icc (0:ℝ) T, 0≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ z, ‖iteratedFDeriv ℝ (k+1) (fun w => s.f (u,w)) z‖≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => s.E (u,y)) x‖≤H u ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.B (u,y)) x‖≤H u) →
      ∀ t∈Icc (0:ℝ) T, ∀ x,
        ‖iteratedFDeriv ℝ (k+1) (fun y => ∫ z in ball (0:Vec) t,
          retardedElectricDensity s t y (y+z)) x‖ ≤ C*(∫ u in Icc (0:ℝ) t, 1+H u) ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => ∫ z in ball (0:Vec) t,
          retardedMagneticDensity s t y (y+z)) x‖ ≤ C*(∫ u in Icc (0:ℝ) t, 1+H u) := by
  sorry

end RVM

end

end OAI
end
