-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_uniform_no_flat_descendant_total_mass
-- name    : OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:36.744443+00:00
-- url     : https://prove2.me/theorems/a9fe8fde-83f9-4cde-bc44-5babcd055c94
-- title:
--   OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass` of [lean/OAI/Analysis/RieszRectifiability/Packing/NoFlatDescendantPacking.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Packing/NoFlatDescendantPacking.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem exists_uniform_no_flat_descendant_total_mass {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
--       (C G A α : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hA : 1 ≤ A) (hα : 0 < α) :
--       ∃ I : ℕ, 0 < I ∧ ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
--         GlobalUpperGrowth n G μ →
--         (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
--           ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
--         (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
--           MemLp (truncated n μ ε f) 2 μ ∧
--             eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
--         ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
--         AdmissibleRadius μ (latticeRadius R₀ k / 8) →
--         ∑' i : NoFlatDescendant n μ R₀ hR₀ k z I A α,
--           μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R₀ hR₀ k z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.HasFlatDescendant`, `OAI.RieszRectifiability.NoFlatDescendant`, `OAI.RieszRectifiability.SupportCellDescendant`, `OAI.RieszRectifiability.cleanSupportCell`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.supportLatticeNets`, `OAI.RieszRectifiability.SeparatedCover` and `OAI.RieszRectifiability.SupportCellDescendant.cell` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius`, `OAI.RieszRectifiability.Ambient` and `OAI.RieszRectifiability.truncated` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Packing/NoFlatDescendantPacking.lean (declaration OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass)

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
open scoped ENNReal NNReal

theorem exists_uniform_no_flat_descendant_total_mass {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G A α : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hA : 1 ≤ A) (hα : 0 < α) :
    ∃ I : ℕ, 0 < I ∧ ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated n μ ε f) 2 μ ∧
          eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      ∑' i : NoFlatDescendant n μ R₀ hR₀ k z I A α,
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R₀ hR₀ k z) := by
  sorry

end

end RieszRectifiability

end OAI
end
