-- Prove2me | Theorems.Thm_OAI_AffineBernstein_balanced_affineMaximal_constant_det
-- name    : OAI.AffineBernstein.balanced_affineMaximal_constant_det
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:10:00.66507+00:00
-- url     : https://prove2.me/theorems/e40082cb-d0fe-4783-8d31-ad2242622b44
-- title:
--   OAI.AffineBernstein.balanced_affineMaximal_constant_det: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.balanced_affineMaximal_constant_det` of [lean/OAI/Analysis/AffineBernstein/ConstantDet.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ConstantDet.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem balanced_affineMaximal_constant_det {n : ℕ} (hn : 1 ≤ n)
--       {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
--       (hm : AffineMaximalOn univ u)
--       {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
--       ∀ x y, (hessian u x).det=(hessian u y).det
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.SectionBalance` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proofs of `OAI.AffineBernstein.balanced_constant_hessian` and `OAI.AffineBernstein.balanced_global_directional_bddAbove` of this split import it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ConstantDet.lean (declaration OAI.AffineBernstein.balanced_affineMaximal_constant_det)

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

section ConstantDetProducer

theorem balanced_affineMaximal_constant_det {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∀ x y, (hessian u x).det=(hessian u y).det := by
  sorry

end ConstantDetProducer

end
end AffineBernstein
end

end OAI
end
