-- Prove2me | Theorems.Thm_OAI_EuclideanFiveColor_four_interface_word_data
-- name    : OAI.EuclideanFiveColor.four_interface_word_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:53:37.178991+00:00
-- url     : https://prove2.me/theorems/f6c90e93-9b65-4519-ad72-18c00e944af2
-- title:
--   OAI.EuclideanFiveColor.four_interface_word_data: intermediate lemma from OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EuclideanFiveColor.four_interface_word_data` of [lean/OAI/Geometry/PlaneColoring/PlaneColoring/Interfaces.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/PlaneColoring/Interfaces.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EuclideanFiveColor`, with `open Set Filter Topology MeasureTheory`, `open scoped RealInnerProductSpace`):
--
--   ```lean
--   lemma four_interface_word_data (hw : WeakColoring 5 c) {x : ℂ} {v : Fin 4 → ℂ}
--       (hv : ∀i,‖v i‖=1)
--       (hcompat : ∀ᵐt∂angularMeasure,InterfaceFourCompatible (fourInterfaceSign v t) (palette c hc x t)) :
--       ∃G : Set Angles,Dense G ∧ (∀t∈G,t+(sixty : Angles)∈G) ∧
--         (∀t∈G,∀j i,⟪direction (t+sixAngle j),v i⟫≠0) ∧
--         (∀t∈G,∀j,fourInterfaceWord hc x t j≠0 → fourInterfaceWord hc x t j=
--           interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j))) ∧
--         (∀t∈G,FourWordValid (fourInterfaceWord hc x t)) ∧
--         ∃ε : ℝ,0<ε ∧ ∀t∈G,∀u∈G,dist t u<ε →
--           FourWordCross (fourInterfaceWord hc x t) (fourInterfaceWord hc x u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EuclideanFiveColor.Angles`, `OAI.EuclideanFiveColor.FourWordCross`, `OAI.EuclideanFiveColor.FourWordValid`, `OAI.EuclideanFiveColor.InterfaceFourCompatible`, `OAI.EuclideanFiveColor.angularMeasure`, `OAI.EuclideanFiveColor.direction` and `OAI.EuclideanFiveColor.palette` (definitions bundle `OAIQ5T4000` of this split); `OAI.EuclideanFiveColor.interfaceFourDiagonal` and `OAI.EuclideanFiveColor.sixty` (definitions bundle `OAIQ5T4001` of this split); `OAI.EuclideanFiveColor.WeakColoring`, `OAI.EuclideanFiveColor.fourInterfaceSign`, `OAI.EuclideanFiveColor.fourInterfaceWord` and `OAI.EuclideanFiveColor.sixAngle` (definitions bundle `OAIQ5T4002` of this split).
--
--   **Used by.** The proof of `OAI.EuclideanFiveColor.annulus_maps_eventually_forest` of this split imports it.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/PlaneColoring/Interfaces.lean (declaration OAI.EuclideanFiveColor.four_interface_word_data)

import Mathlib
import Definitions.Def_OAIQ5T4002

section

attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {c : ℂ → Fin 5} (hc : Measurable c)
lemma four_interface_word_data (hw : WeakColoring 5 c) {x : ℂ} {v : Fin 4 → ℂ}
    (hv : ∀i,‖v i‖=1)
    (hcompat : ∀ᵐt∂angularMeasure,InterfaceFourCompatible (fourInterfaceSign v t) (palette c hc x t)) :
    ∃G : Set Angles,Dense G ∧ (∀t∈G,t+(sixty : Angles)∈G) ∧
      (∀t∈G,∀j i,⟪direction (t+sixAngle j),v i⟫≠0) ∧
      (∀t∈G,∀j,fourInterfaceWord hc x t j≠0 → fourInterfaceWord hc x t j=
        interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j))) ∧
      (∀t∈G,FourWordValid (fourInterfaceWord hc x t)) ∧
      ∃ε : ℝ,0<ε ∧ ∀t∈G,∀u∈G,dist t u<ε →
        FourWordCross (fourInterfaceWord hc x t) (fourInterfaceWord hc x u) := by
  sorry
end EuclideanFiveColor
end

end OAI
end
