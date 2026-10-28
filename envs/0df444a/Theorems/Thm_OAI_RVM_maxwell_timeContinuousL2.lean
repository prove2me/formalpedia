-- Prove2me | Theorems.Thm_OAI_RVM_maxwell_timeContinuousL2
-- name    : OAI.RVM.maxwell_timeContinuousL2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:27:15.978998+00:00
-- url     : https://prove2.me/theorems/355da999-54d1-4882-bbfb-71aa317b208c
-- title:
--   OAI.RVM.maxwell_timeContinuousL2: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.maxwell_timeContinuousL2` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/VlasovConstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/VlasovConstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`):
--
--   ```lean
--   lemma maxwell_timeContinuousL2 {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
--       (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
--       (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
--       (hE0 : MemLp E₀ 2 volume) (hB0 : MemLp B₀ 2 volume)
--       (hDE : ∀ x, divergence E₀ x=ρ (0,x)) (hDB : ∀ x, divergence B₀ x=0)
--       (hK : ∀ T, 0 ≤ T → ∃ R : ℝ, ∀ s∈Icc (-1) (T+1), ∀ y : Vec,
--         R<‖y‖ → ρ (s,y)=0 ∧ j (s,y)=0) :
--       TimeContinuousL2 (maxwellElectric E₀ B₀ ρ j) ∧
--       TimeContinuousL2 (maxwellMagnetic E₀ B₀ j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.maxwellElectric` and `OAI.RVM.maxwellMagnetic` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Field`, `OAI.RVM.TimeContinuousL2`, `OAI.RVM.Vec` and `OAI.RVM.divergence` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.exists_picard_regular` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/VlasovConstruction.lean (declaration OAI.RVM.maxwell_timeContinuousL2)

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
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma maxwell_timeContinuousL2 {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
    (hE0 : MemLp E₀ 2 volume) (hB0 : MemLp B₀ 2 volume)
    (hDE : ∀ x, divergence E₀ x=ρ (0,x)) (hDB : ∀ x, divergence B₀ x=0)
    (hK : ∀ T, 0 ≤ T → ∃ R : ℝ, ∀ s∈Icc (-1) (T+1), ∀ y : Vec,
      R<‖y‖ → ρ (s,y)=0 ∧ j (s,y)=0) :
    TimeContinuousL2 (maxwellElectric E₀ B₀ ρ j) ∧
    TimeContinuousL2 (maxwellMagnetic E₀ B₀ j) := by
  sorry

end RVM

end

end OAI
end
