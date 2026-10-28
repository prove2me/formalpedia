-- Prove2me | Theorems.Thm_OAI_RVM_Magnetic_classical_magnetic_gradient_volterra_bound
-- name    : OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:15:25.066405+00:00
-- url     : https://prove2.me/theorems/d8c685dc-8b3f-4b2f-8d1c-c3dab1a52a3d
-- title:
--   OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound` of [lean/OAI/Analysis/VlasovMaxwell/Regularity/PhysicalGradient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/PhysicalGradient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM.Magnetic`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma classical_magnetic_gradient_volterra_bound {d : Datum} (hd : Admissible d)
--       (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hH : 0≤H) :
--       ∃ B C D K : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧ 0≤K ∧
--       ∀ (s : Solution) (U t N : ℝ) (x : Vec) (g : ℝ → ℝ),
--         ClassicalBefore d s U → SmoothOnFiniteHorizons s →
--         0<t → t<U → U≤H → 0≤N → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
--         (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
--         |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+D*Real.log (1+C*N)+K*(∫ u in Icc (0:ℝ) t,1+g u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClassicalBefore` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.SmoothOnFiniteHorizons`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.prefix_spatial_gradient_volterra` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/PhysicalGradient.lean (declaration OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound)

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

namespace Magnetic

lemma classical_magnetic_gradient_volterra_bound {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D K : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧ 0≤K ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → 0≤N → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+D*Real.log (1+C*N)+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  sorry

end Magnetic

end RVM

end

end OAI
end
