-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_uniform_bad_descendant_total_mass
-- name    : OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:40.199592+00:00
-- url     : https://prove2.me/theorems/690cdd4b-1caf-4d00-91c8-79bbad00ae29
-- title:
--   OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass` of [lean/OAI/Analysis/RieszRectifiability/Nets/LatticeOscillationTotalMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Nets/LatticeOscillationTotalMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem exists_uniform_bad_descendant_total_mass (p d : ℕ) [Nontrivial (Ambient d)]
--       (C G J v : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hJ : 0 < J) (hv : 0 < v) :
--       ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
--         GlobalUpperGrowth (p + 1) G μ →
--         (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
--           ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
--         (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
--           MemLp (truncated (p + 1) μ ε f) 2 μ ∧
--             eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
--         ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
--         AdmissibleRadius μ (latticeRadius R k / 8) →
--           ∑' i : BadSupportDescendant (p + 1) μ R hR k z J v, μ i.val.cell ≤
--             ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.BadSupportDescendant`, `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.ScalarOscillationBound`, `OAI.RieszRectifiability.SupportCellDescendant`, `OAI.RieszRectifiability.cleanSupportCell`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.supportLatticeNets`, `OAI.RieszRectifiability.SeparatedCover`, `OAI.RieszRectifiability.SupportCellDescendant.cell` and `OAI.RieszRectifiability.SupportCellDescendant.radius` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius`, `OAI.RieszRectifiability.Ambient` and `OAI.RieszRectifiability.truncated` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Nets/LatticeOscillationTotalMass.lean (declaration OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass)

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

theorem exists_uniform_bad_descendant_total_mass (p d : ℕ) [Nontrivial (Ambient d)]
    (C G J v : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hJ : 0 < J) (hv : 0 < v) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ ε f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
        ∑' i : BadSupportDescendant (p + 1) μ R hR k z J v, μ i.val.cell ≤
          ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  sorry

end

end RieszRectifiability

end OAI
end
