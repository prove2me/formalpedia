-- Prove2me | Theorems.Thm_OAI_RVM_classical_fields_curvature_volterra_bound
-- name    : OAI.RVM.classical_fields_curvature_volterra_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:22:38.056444+00:00
-- url     : https://prove2.me/theorems/e1a74c14-e24e-4dde-9ce0-5eb59cc956a2
-- title:
--   OAI.RVM.classical_fields_curvature_volterra_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.classical_fields_curvature_volterra_bound` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/VolterraKernels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/VolterraKernels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma classical_fields_curvature_volterra_bound {d : Datum} (hd : Admissible d)
--       (A P L M N R : ℝ) (hM : 0≤M) (hN : 0≤N) (hR : 0≤R) :
--       ∃ D K : ℝ,0≤D ∧ 0≤K ∧ ∀ (s : Solution) (U t : ℝ) (g : ℝ → ℝ),
--         ClassicalBefore d s U → SmoothOnFiniteHorizons s → 0<t → t<U → U≤R →
--         Continuous g → (∀ r∈Icc (0:ℝ) U,0≤g r) →
--         (∀ r∈Icc (0:ℝ) U,∀ x v,|s.f (r,x,v)|≤A) →
--         (∀ r∈Icc (0:ℝ) U,∀ x v,P<‖v‖ → s.f (r,x,v)=0) →
--         (∀ r∈Icc (0:ℝ) U,∀ x,‖s.E (r,x)‖≤L ∧ ‖s.B (r,x)‖≤L) →
--         (∀ r∈Icc (0:ℝ) U,∀ v,CurvatureBound (fun x => s.f (r,x,v)) (g r)) →
--         (∀ r∈Icc (0:ℝ) U,CurvatureBound (fun x => s.E (r,x)) (g r) ∧ CurvatureBound (fun x => s.B (r,x)) (g r)) →
--         (∀ r∈Icc (0:ℝ) U,∀ v x y,|s.f (r,y,v)-s.f (r,x,v)|≤M*‖y-x‖) →
--         SpatialFieldLip U N s.E s.B →
--         CurvatureBound (fun x => s.E (t,x)) (D+K*(∫ r in Icc (0:ℝ) t,1+g r)) ∧
--         CurvatureBound (fun x => s.B (t,x)) (D+K*(∫ r in Icc (0:ℝ) t,1+g r))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClassicalBefore`, `OAI.RVM.CurvatureBound` and `OAI.RVM.SpatialFieldLip` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.SmoothOnFiniteHorizons`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.prefix_second_jet_volterra` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/VolterraKernels.lean (declaration OAI.RVM.classical_fields_curvature_volterra_bound)

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

lemma classical_fields_curvature_volterra_bound {d : Datum} (hd : Admissible d)
    (A P L M N R : ℝ) (hM : 0≤M) (hN : 0≤N) (hR : 0≤R) :
    ∃ D K : ℝ,0≤D ∧ 0≤K ∧ ∀ (s : Solution) (U t : ℝ) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s → 0<t → t<U → U≤R →
      Continuous g → (∀ r∈Icc (0:ℝ) U,0≤g r) →
      (∀ r∈Icc (0:ℝ) U,∀ x v,|s.f (r,x,v)|≤A) →
      (∀ r∈Icc (0:ℝ) U,∀ x v,P<‖v‖ → s.f (r,x,v)=0) →
      (∀ r∈Icc (0:ℝ) U,∀ x,‖s.E (r,x)‖≤L ∧ ‖s.B (r,x)‖≤L) →
      (∀ r∈Icc (0:ℝ) U,∀ v,CurvatureBound (fun x => s.f (r,x,v)) (g r)) →
      (∀ r∈Icc (0:ℝ) U,CurvatureBound (fun x => s.E (r,x)) (g r) ∧ CurvatureBound (fun x => s.B (r,x)) (g r)) →
      (∀ r∈Icc (0:ℝ) U,∀ v x y,|s.f (r,y,v)-s.f (r,x,v)|≤M*‖y-x‖) →
      SpatialFieldLip U N s.E s.B →
      CurvatureBound (fun x => s.E (t,x)) (D+K*(∫ r in Icc (0:ℝ) t,1+g r)) ∧
      CurvatureBound (fun x => s.B (t,x)) (D+K*(∫ r in Icc (0:ℝ) t,1+g r)) := by
  sorry

end RVM

end

end OAI
end
