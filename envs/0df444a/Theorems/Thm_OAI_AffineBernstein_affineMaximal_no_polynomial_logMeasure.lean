-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_no_polynomial_logMeasure
-- name    : OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:08:43.709341+00:00
-- url     : https://prove2.me/theorems/782af3fe-8864-40f4-b249-25a101b71a4c
-- title:
--   OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure` of [lean/OAI/Analysis/AffineBernstein/ActualLogGrowth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualLogGrowth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter Metric`, `open scoped Topology`, `open Filter`):
--
--   ```lean
--   theorem affineMaximal_no_polynomial_logMeasure {n k l₀ : ℕ}
--       (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hkn : k ≤ n)
--       {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
--       (Ω : ℕ → Set (Space n)) (u : ℕ → Space n → ℝ)
--       (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × E) ≃L[ℝ] (Space n × ℝ))
--       (D : ℕ → Set (Space k)) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (hΩ : ∀ j, IsOpen (Ω j)) (hcv : ∀ j, Convex ℝ (Ω j))
--       (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (Ω j))
--       (hp : ∀ j x, x ∈ Ω j → (hessian (u j) x).PosDef)
--       (hm : ∀ j, AffineMaximalOn (Ω j) (u j))
--       (hD : ∀ j, IsOpen (D j)) (hDpos : ∀ j, D j ⊆ positiveOrthant k)
--       (hK : ∀ j s, s ∈ D j → IsCompact {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
--       (hzero : ∀ j s, s ∈ D j →
--         (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
--       (havail : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop, logarithmicBox k R ⊆ logSpace '' (D j))
--       {c C : ℝ} (hc : 0 < c)
--       (hpos : ∀ᶠ j in atTop, c ≤
--         (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k l₀))
--       (hupper : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop,
--         (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k R) ≤
--           C*(R+1:ℝ)^k) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphLogMeasure`, `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.logSpace`, `OAI.AffineBernstein.logarithmicBox` and `OAI.AffineBernstein.positiveOrthant` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualLogGrowth.lean (declaration OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure)

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
open Filter Metric
open scoped Topology

open Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem affineMaximal_no_polynomial_logMeasure {n k l₀ : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hkn : k ≤ n)
    {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    (Ω : ℕ → Set (Space n)) (u : ℕ → Space n → ℝ)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × E) ≃L[ℝ] (Space n × ℝ))
    (D : ℕ → Set (Space k)) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hΩ : ∀ j, IsOpen (Ω j)) (hcv : ∀ j, Convex ℝ (Ω j))
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (Ω j))
    (hp : ∀ j x, x ∈ Ω j → (hessian (u j) x).PosDef)
    (hm : ∀ j, AffineMaximalOn (Ω j) (u j))
    (hD : ∀ j, IsOpen (D j)) (hDpos : ∀ j, D j ⊆ positiveOrthant k)
    (hK : ∀ j s, s ∈ D j → IsCompact {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
    (hzero : ∀ j s, s ∈ D j →
      (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
    (havail : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop, logarithmicBox k R ⊆ logSpace '' (D j))
    {c C : ℝ} (hc : 0 < c)
    (hpos : ∀ᶠ j in atTop, c ≤
      (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k l₀))
    (hupper : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop,
      (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k R) ≤
        C*(R+1:ℝ)^k) : False := by
  sorry

end AffineBernstein

end

end OAI
end
