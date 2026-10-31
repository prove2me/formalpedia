-- Prove2me | Theorems.Thm_OAI_AffineBernstein_normalized_balanced_det_bounds
-- name    : OAI.AffineBernstein.normalized_balanced_det_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:10:38.394998+00:00
-- url     : https://prove2.me/theorems/610caab3-d850-4589-ac5d-03235f6b126b
-- title:
--   OAI.AffineBernstein.normalized_balanced_det_bounds: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.normalized_balanced_det_bounds` of [lean/OAI/Analysis/AffineBernstein/NormalizedFamilyDet.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NormalizedFamilyDet.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem normalized_balanced_det_bounds {n : ℕ} {ρ R : ℝ}
--       (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
--       ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ v : Space n → ℝ,
--         ContDiff ℝ ∞ v → (∀ x, (hessian v x).PosDef) →
--         AffineMaximalOn univ v → v 0=0 → fderiv ℝ v 0=0 →
--         SectionBalance univ v ρ →
--         Metric.ball 0 1 ⊆ tangentSection univ v 0 1 →
--         tangentSection univ v 0 1 ⊆ Metric.ball 0 R →
--         ∀ x ∈ Metric.ball (0:Space n) (1/8:ℝ),
--           c ≤ (hessian v x).det ∧ (hessian v x).det ≤ C
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.SectionBalance` and `OAI.AffineBernstein.tangentSection` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proofs of `OAI.AffineBernstein.balanced_affineMaximal_constant_det`, `OAI.AffineBernstein.balanced_global_directional_bddAbove`, `OAI.AffineBernstein.normalized_critical_density` and `OAI.AffineBernstein.normalized_log_variance` of this split import it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NormalizedFamilyDet.lean (declaration OAI.AffineBernstein.normalized_balanced_det_bounds)

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedFamilyDet

theorem normalized_balanced_det_bounds {n : ℕ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ v : Space n → ℝ,
      ContDiff ℝ ∞ v → (∀ x, (hessian v x).PosDef) →
      AffineMaximalOn univ v → v 0=0 → fderiv ℝ v 0=0 →
      SectionBalance univ v ρ →
      Metric.ball 0 1 ⊆ tangentSection univ v 0 1 →
      tangentSection univ v 0 1 ⊆ Metric.ball 0 R →
      ∀ x ∈ Metric.ball (0:Space n) (1/8:ℝ),
        c ≤ (hessian v x).det ∧ (hessian v x).det ≤ C := by
  sorry

end NormalizedFamilyDet

end
end AffineBernstein
end

end OAI
end
