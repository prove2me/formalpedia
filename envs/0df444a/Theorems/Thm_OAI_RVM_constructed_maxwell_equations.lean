-- Prove2me | Theorems.Thm_OAI_RVM_constructed_maxwell_equations
-- name    : OAI.RVM.constructed_maxwell_equations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:23:30.599418+00:00
-- url     : https://prove2.me/theorems/fdf7fa63-dc0e-47fb-8894-a93825e61d62
-- title:
--   OAI.RVM.constructed_maxwell_equations: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.constructed_maxwell_equations` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceField.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceField.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`):
--
--   ```lean
--   theorem constructed_maxwell_equations {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
--       (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
--       (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
--       (hcont : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0)
--       (hDE : ∀ x, divergence E₀ x=ρ (0,x)) (hDB : ∀ x, divergence B₀ x=0)
--       {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
--       let E := maxwellElectric E₀ B₀ ρ j
--       let B := maxwellMagnetic E₀ B₀ j
--       dirD E (1,0) (t,x)=spaceCurl B (t,x)-j (t,x) ∧
--       dirD B (1,0) (t,x)= -spaceCurl E (t,x) ∧
--       spaceDiv E (t,x)=ρ (t,x) ∧ spaceDiv B (t,x)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.dirD`, `OAI.RVM.maxwellElectric`, `OAI.RVM.maxwellMagnetic`, `OAI.RVM.spaceCurl` and `OAI.RVM.spaceDiv` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Field`, `OAI.RVM.Vec` and `OAI.RVM.divergence` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.exists_picard_regular` and `OAI.RVM.maxwell_timeContinuousL2` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceField.lean (declaration OAI.RVM.constructed_maxwell_equations)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

theorem constructed_maxwell_equations {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
    (hcont : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0)
    (hDE : ∀ x, divergence E₀ x=ρ (0,x)) (hDB : ∀ x, divergence B₀ x=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    let E := maxwellElectric E₀ B₀ ρ j
    let B := maxwellMagnetic E₀ B₀ j
    dirD E (1,0) (t,x)=spaceCurl B (t,x)-j (t,x) ∧
    dirD B (1,0) (t,x)= -spaceCurl E (t,x) ∧
    spaceDiv E (t,x)=ρ (t,x) ∧ spaceDiv B (t,x)=0 := by
  sorry

end RVM
end

end OAI
end
