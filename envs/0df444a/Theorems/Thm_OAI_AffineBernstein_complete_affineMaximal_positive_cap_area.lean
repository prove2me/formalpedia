-- Prove2me | Theorems.Thm_OAI_AffineBernstein_complete_affineMaximal_positive_cap_area
-- name    : OAI.AffineBernstein.complete_affineMaximal_positive_cap_area
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:10:20.133597+00:00
-- url     : https://prove2.me/theorems/b88c3ee1-7e94-4bb0-81c6-8b91f637e8c5
-- title:
--   OAI.AffineBernstein.complete_affineMaximal_positive_cap_area: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.complete_affineMaximal_positive_cap_area` of [lean/OAI/Analysis/AffineBernstein/CompletePositiveCapFurther.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/CompletePositiveCapFurther.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem complete_affineMaximal_positive_cap_area {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (hm : AffineMaximalOn Ω u) (hc : EuclideanGraphComplete Ω u)
--       (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
--       {C : Set (Space n × ℝ)} (hC : IsClosed C)
--       (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
--       (ell : (Space n × ℝ) →L[ℝ] ℝ) (hell : ell ≠ 0)
--       {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | ell z ≤ b}))
--       {o : Space n × ℝ} (ho : o ∈ interior C) (hob : ell o < b) :
--       ∃ c > 0, ∀ᶠ j in atTop, c ≤ affineImageLinearCapArea Ω u (L j) (v j) ell b
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.LocalDistanceConverges`, `OAI.AffineBernstein.affineImageLinearCapArea` and `OAI.AffineBernstein.sourceEpigraph` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.EuclideanGraphComplete`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proofs of `OAI.AffineBernstein.complete_affineMaximal_model_transverse_pos` and `OAI.AffineBernstein.normalized_model_positive_face_mass` of this split import it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/CompletePositiveCapFurther.lean (declaration OAI.AffineBernstein.complete_affineMaximal_positive_cap_area)

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

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

theorem complete_affineMaximal_positive_cap_area {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (hc : EuclideanGraphComplete Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hell : ell ≠ 0)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | ell z ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : ell o < b) :
    ∃ c > 0, ∀ᶠ j in atTop, c ≤ affineImageLinearCapArea Ω u (L j) (v j) ell b := by
  sorry

end AffineBernstein

end

end OAI
end
