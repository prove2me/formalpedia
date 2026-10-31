-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_det_upper_of_section_control
-- name    : OAI.AffineBernstein.affineMaximal_det_upper_of_section_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:07:31.095289+00:00
-- url     : https://prove2.me/theorems/87d3a177-e447-40e9-841c-837f5873faaf
-- title:
--   OAI.AffineBernstein.affineMaximal_det_upper_of_section_control: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_det_upper_of_section_control` of [lean/OAI/Analysis/AffineBernstein/LocalDet.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/LocalDet.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   lemma affineMaximal_det_upper_of_section_control {n : ℕ} {O : Set (Space n)}
--       (hO : IsOpen O) (hcv : Convex ℝ O) {f : Space n → ℝ}
--       (hf : ContDiffOn ℝ ∞ f O) (hp : ∀ x ∈ O, (hessian f x).PosDef)
--       (hm : AffineMaximalOn O f) {a : Space n} {r h M : ℝ}
--       (hr : 0 < r) (hh : 0 < h) (hM : 0 ≤ M)
--       (hball : Metric.closedBall a (2*r) ⊆ O)
--       (hb : ∀ x ∈ O, |f x| ≤ M)
--       (hsection : tangentSection O f a (2*h) ⊆ Metric.ball a r) :
--       (hessian f a).det ≤
--         (2*(n:ℝ)*(((n:ℝ)+2)*(2*((4*M/r)^2+1))+(4*M/r)^2))^n * h^2 *
--           Real.exp ((4*M/r)^2/(4*((4*M/r)^2+1))) / h^(n+2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.tangentSection` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.normalized_balanced_det_bounds` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/LocalDet.lean (declaration OAI.AffineBernstein.affineMaximal_det_upper_of_section_control)

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

section LocalDetProducer

lemma affineMaximal_det_upper_of_section_control {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hcv : Convex ℝ O) {f : Space n → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) (hp : ∀ x ∈ O, (hessian f x).PosDef)
    (hm : AffineMaximalOn O f) {a : Space n} {r h M : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hM : 0 ≤ M)
    (hball : Metric.closedBall a (2*r) ⊆ O)
    (hb : ∀ x ∈ O, |f x| ≤ M)
    (hsection : tangentSection O f a (2*h) ⊆ Metric.ball a r) :
    (hessian f a).det ≤
      (2*(n:ℝ)*(((n:ℝ)+2)*(2*((4*M/r)^2+1))+(4*M/r)^2))^n * h^2 *
        Real.exp ((4*M/r)^2/(4*((4*M/r)^2+1))) / h^(n+2) := by
  sorry

end LocalDetProducer

end
end AffineBernstein
end

end OAI
end
