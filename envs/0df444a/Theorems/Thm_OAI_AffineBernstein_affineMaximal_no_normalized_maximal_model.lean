-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_no_normalized_maximal_model
-- name    : OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:08:24.701351+00:00
-- url     : https://prove2.me/theorems/02966fa5-1efd-4eb4-81e6-0d1137eaf622
-- title:
--   OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model` of [lean/OAI/Analysis/AffineBernstein/NoNormalizedMaximalModel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NoNormalizedMaximalModel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Metric Filter`):
--
--   ```lean
--   theorem affineMaximal_no_normalized_maximal_model {n k m d : ℕ}
--       (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hm : 1 ≤ m)
--       (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
--       (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
--       {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
--       {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
--       (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
--       (hcomplete : EuclideanGraphComplete Ω u)
--       (hmax : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
--         IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False)
--       (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
--       {C : Set (Space k × Space m)} (hC : IsModelShape C)
--       (hf : InAffineLimitFamily (sourceEpigraph Ω u) C)
--       (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
--       {r R₀ : ℝ} (hr : 0 < r)
--       (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
--       (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.InAffineLimitFamily`, `OAI.AffineBernstein.IsModelShape`, `OAI.AffineBernstein.LocalDistanceConverges`, `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.modelFiber` and `OAI.AffineBernstein.sourceEpigraph` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.EuclideanGraphComplete`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affine_bernstein` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NoNormalizedMaximalModel.lean (declaration OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model)

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

open Metric Filter
theorem affineMaximal_no_normalized_maximal_model {n k m d : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (hmax : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) : False := by
  sorry

open Filter Metric
open scoped Topology Pointwise

open scoped Pointwise

open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

end AffineBernstein

end

end OAI
end
