-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_uniform_cell_flat_annular_alternative
-- name    : OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:58.076193+00:00
-- url     : https://prove2.me/theorems/36f61944-f35f-4ff1-a876-df0e107a740b
-- title:
--   OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative` of [lean/OAI/Analysis/RieszRectifiability/Flatness/CellFlatAnnularAlternative.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Flatness/CellFlatAnnularAlternative.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set`):
--
--   ```lean
--   theorem exists_uniform_cell_flat_annular_alternative {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
--       (C G B ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
--       ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 16 ∧ ∀ μ : Measure (Ambient d),
--         GlobalUpperGrowth n G μ →
--         (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
--           ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
--         ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
--         AdmissibleRadius μ (latticeRadius R₀ k / 8) →
--         HasFlatBallAbove n μ (ball (z : Ambient d) (latticeRadius R₀ k / 16))
--           (ρ * latticeRadius R₀ k) (latticeRadius R₀ k / 16) ε ∨
--           HasLargeCellAnnulus n μ R₀ hR₀ k z ρ B
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.HasFlatBallAbove`, `OAI.RieszRectifiability.HasLargeCellAnnulus`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.supportLatticeNets` and `OAI.RieszRectifiability.SeparatedCover` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Flatness/CellFlatAnnularAlternative.lean (declaration OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative)

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_cell_flat_annular_alternative {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G B ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 16 ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      HasFlatBallAbove n μ (ball (z : Ambient d) (latticeRadius R₀ k / 16))
        (ρ * latticeRadius R₀ k) (latticeRadius R₀ k / 16) ε ∨
        HasLargeCellAnnulus n μ R₀ hR₀ k z ρ B := by
  sorry

end

end RieszRectifiability

end OAI
end
