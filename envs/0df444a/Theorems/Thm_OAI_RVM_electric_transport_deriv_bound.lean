-- Prove2me | Theorems.Thm_OAI_RVM_electric_transport_deriv_bound
-- name    : OAI.RVM.electric_transport_deriv_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:24:28.472173+00:00
-- url     : https://prove2.me/theorems/c6c784db-e059-4fec-b8fa-5ced6fbcaa6f
-- title:
--   OAI.RVM.electric_transport_deriv_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.electric_transport_deriv_bound` of [lean/OAI/Analysis/VlasovMaxwell/Flow/TransportDifferentiation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Flow/TransportDifferentiation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma electric_transport_deriv_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
--       (hA : 0≤A) (hH : 0≤H) :
--       ∃ B C D : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧
--       ∀ (s : Solution) (U t N : ℝ) (x : Vec),
--         0<t → t≤U → U≤H → 0≤N →
--         ContDiffOn ℝ 1 s.f particleHalfSpace →
--         ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
--         CompactOnFiniteHorizons s → EquationsBefore s U →
--         (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
--         |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t, ∫ v,
--           transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
--           B+D*(Real.log (max 1 H)+Real.log (1+C*N))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EquationsBefore`, `OAI.RVM.coneRadius` and `OAI.RVM.transportConeCoefficient` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.CompactOnFiniteHorizons`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.fieldHalfSpace` and `OAI.RVM.particleHalfSpace` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.classical_electric_log_closed_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Flow/TransportDifferentiation.lean (declaration OAI.RVM.electric_transport_deriv_bound)

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

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

lemma electric_transport_deriv_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t, ∫ v,
        transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
        B+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  sorry

end RVM

end

end OAI
end
