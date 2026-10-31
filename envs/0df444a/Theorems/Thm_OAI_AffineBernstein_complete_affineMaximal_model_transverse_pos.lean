-- Prove2me | Theorems.Thm_OAI_AffineBernstein_complete_affineMaximal_model_transverse_pos
-- name    : OAI.AffineBernstein.complete_affineMaximal_model_transverse_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:09:54.58887+00:00
-- url     : https://prove2.me/theorems/a3baad04-8df1-4810-89a1-59ab8e18208a
-- title:
--   OAI.AffineBernstein.complete_affineMaximal_model_transverse_pos: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.complete_affineMaximal_model_transverse_pos` of [lean/OAI/Analysis/AffineBernstein/NoZeroTransverse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NoZeroTransverse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem complete_affineMaximal_model_transverse_pos {n k m : ℕ} (hn : 0 < n)
--       {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
--       {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
--       (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
--       (hc : EuclideanGraphComplete Ω u)
--       {C : Set (Space k × Space m)} (hC : IsModelShape C)
--       (hf : InAffineLimitFamily (sourceEpigraph Ω u) C) : 1 ≤ m
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.InAffineLimitFamily`, `OAI.AffineBernstein.IsModelShape` and `OAI.AffineBernstein.sourceEpigraph` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.EuclideanGraphComplete`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affine_bernstein` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NoZeroTransverse.lean (declaration OAI.AffineBernstein.complete_affineMaximal_model_transverse_pos)

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

section NoZeroTransverse

theorem complete_affineMaximal_model_transverse_pos {n k m : ℕ} (hn : 0 < n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u)
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C) : 1 ≤ m := by
  sorry
end NoZeroTransverse

end
end AffineBernstein
end

end OAI
end
