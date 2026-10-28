-- Prove2me | Theorems.Thm_OAI_SKGap_compact_conditional_uniform_tail
-- name    : OAI.SKGap.compact_conditional_uniform_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:49.932234+00:00
-- url     : https://prove2.me/theorems/82fadc25-e736-422e-9c50-c9464d7b7694
-- title:
--   OAI.SKGap.compact_conditional_uniform_tail: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.compact_conditional_uniform_tail` of [lean/OAI/Probability/SKGap/Gaussian/ConditionalUniformTail.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Gaussian/ConditionalUniformTail.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix MeasureTheory ProbabilityTheory Real Set`, `open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius`):
--
--   ```lean
--   theorem compact_conditional_uniform_tail {α : Type*} [TopologicalSpace α] [CompactSpace α]
--       {j A : ℝ} (hj : 0 < j) (hj1 : j < 1) (hA : 0 < A)
--       (hsub : sqrt j*A < 1)
--       (b e s q κ : α → ℝ) (hb : Continuous b) (he : Continuous e)
--       (hs : Continuous s) (hq : Continuous q) (hk : Continuous κ)
--       (hb0 : ∀ x,0 < b x) (hb1 : ∀ x,b x ≤ 1) (he0 : ∀ x,0 ≤ e x)
--       (hs0 : ∀ x,0 < s x) (hq0 : ∀ x,0 < q x)
--       (hkq : ∀ x,κ x^2=1-j*q x/s x) :
--       ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
--       ∀ U : ℝ, 0 ≤ U → ∀ ε τ : ℝ, 0 < ε → 0 < τ → ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧ 0 < N ∧
--       ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ A) →
--       0 < j/(n:ℝ)*∑ i,a i →
--       augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε < ρ/2 →
--       ∀ p : Fin 3 → EuclideanSpace ℝ (Fin n), ∀ u : EuclideanSpace ℝ (Fin n),
--       (∀ r,‖p r‖ ≤ U) → ‖u‖ ≤ U → u.ofLp⬝ᵥu.ofLp=1 →
--       ∀ x (C E : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ),
--       C.IsHermitian → E.IsHermitian → τ*‖E‖ < ρ/2 →
--       ‖diagonalAugmentedGram a p-augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x))‖ < ρ/2 →
--       ‖C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
--         j ((κ x-1)*√(j*b x)/√(q x))‖ < ρ/2 →
--       (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
--         {g | ¬(conditionalBase j a g-
--           pathDiagonal a 1*conditionalUpdateColumns j a p u g*
--           (C+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E)*
--           (conditionalUpdateColumns j a p u g)ᵀ*pathDiagonal a 1-
--           (δ*((1-sqrt j*A)^2/4)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ≤
--         101*exp (-c*(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.augmentedGram`, `OAI.SKGap.augmentedGramTolerance`, `OAI.SKGap.conditionalBase`, `OAI.SKGap.conditionalCoefficient`, `OAI.SKGap.conditionalUpdateColumns`, `OAI.SKGap.diagonalAugmentedGram`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.limitingGram`, `OAI.SKGap.matrixBilinear` and `OAI.SKGap.pathDiagonal` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.conditional_empirical_simultaneous` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Gaussian/ConditionalUniformTail.lean (declaration OAI.SKGap.compact_conditional_uniform_tail)

import Mathlib
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

theorem compact_conditional_uniform_tail {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {j A : ℝ} (hj : 0 < j) (hj1 : j < 1) (hA : 0 < A)
    (hsub : sqrt j*A < 1)
    (b e s q κ : α → ℝ) (hb : Continuous b) (he : Continuous e)
    (hs : Continuous s) (hq : Continuous q) (hk : Continuous κ)
    (hb0 : ∀ x,0 < b x) (hb1 : ∀ x,b x ≤ 1) (he0 : ∀ x,0 ≤ e x)
    (hs0 : ∀ x,0 < s x) (hq0 : ∀ x,0 < q x)
    (hkq : ∀ x,κ x^2=1-j*q x/s x) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
    ∀ U : ℝ, 0 ≤ U → ∀ ε τ : ℝ, 0 < ε → 0 < τ → ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧ 0 < N ∧
    ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ A) →
    0 < j/(n:ℝ)*∑ i,a i →
    augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε < ρ/2 →
    ∀ p : Fin 3 → EuclideanSpace ℝ (Fin n), ∀ u : EuclideanSpace ℝ (Fin n),
    (∀ r,‖p r‖ ≤ U) → ‖u‖ ≤ U → u.ofLp⬝ᵥu.ofLp=1 →
    ∀ x (C E : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ),
    C.IsHermitian → E.IsHermitian → τ*‖E‖ < ρ/2 →
    ‖diagonalAugmentedGram a p-augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x))‖ < ρ/2 →
    ‖C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
      j ((κ x-1)*√(j*b x)/√(q x))‖ < ρ/2 →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | ¬(conditionalBase j a g-
        pathDiagonal a 1*conditionalUpdateColumns j a p u g*
        (C+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E)*
        (conditionalUpdateColumns j a p u g)ᵀ*pathDiagonal a 1-
        (δ*((1-sqrt j*A)^2/4)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ≤
      101*exp (-c*(n:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end
