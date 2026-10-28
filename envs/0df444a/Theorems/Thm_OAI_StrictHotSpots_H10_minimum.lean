-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_H10_minimum
-- name    : OAI.StrictHotSpots.H10.minimum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:05:30.308781+00:00
-- url     : https://prove2.me/theorems/d62668b9-1b68-4d32-b54b-c80273804168
-- title:
--   OAI.StrictHotSpots.H10.minimum: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.H10.minimum` of [lean/OAI/Analysis/HotSpots/HotSpots/Dirichlet.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Dirichlet.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.H10`, with `open Set MeasureTheory Filter`, `open scoped ENNReal Topology InnerProductSpace`):
--
--   ```lean
--   lemma minimum (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
--       ∃ (lam : ℝ) (φ : H10 hΩ), 0 < lam ∧ value hΩ φ ≠ 0 ∧
--         (∀ v, lam * ‖value hΩ v‖^2 ≤ ‖grad hΩ v‖^2) ∧
--         (∀ v, inner ℝ (grad hΩ φ) (grad hΩ v) =
--           lam * inner ℝ (value hΩ φ) (value hΩ v))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H10`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.H10.grad` and `OAI.StrictHotSpots.H10.value` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.H10.subcritical` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Dirichlet.lean (declaration OAI.StrictHotSpots.H10.minimum)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho000

section

attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section DirichletMinimumCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)

lemma minimum (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    ∃ (lam : ℝ) (φ : H10 hΩ), 0 < lam ∧ value hΩ φ ≠ 0 ∧
      (∀ v, lam * ‖value hΩ v‖^2 ≤ ‖grad hΩ v‖^2) ∧
      (∀ v, inner ℝ (grad hΩ φ) (grad hΩ v) =
        lam * inner ℝ (value hΩ φ) (value hΩ v)) := by
  sorry

end StrictHotSpots.H10
end DirichletMinimumCombinedLayer

end

end DouglasLipschitzBase

end OAI
end
