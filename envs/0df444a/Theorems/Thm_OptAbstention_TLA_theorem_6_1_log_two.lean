-- Prove2me | Theorems.Thm_OptAbstention_TLA_theorem_6_1_log_two
-- name    : OptAbstention.TLA.theorem_6_1_log_two
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:19:10.095887+00:00
-- url     : https://prove2.me/theorems/5722a1c4-4616-42d9-99f6-021a33ed6cb0
-- title:
--   Theorem 6.1 with log(2/δ) (corrected: the printed log(1/δ) bound vanishes as δ → 1)
-- statement:
--   **Source:** Theorem 6.1 with sample complexity $\mathrm{poly}(M_{D,\ell} B (d+1)^\ell/(\varepsilon\eta)) \cdot \log(1/\delta)$ and runtime $\mathrm{poly}(|S_{\mathrm{test}}|, M_{D,\ell} B (d+1)^\ell/(\varepsilon\eta)) \cdot \log(1/\delta)$.
--
--   **Variant:** the same statement with $\log(2/\delta)$ in place of $\log(1/\delta)$ in both bounds, which is what Lemma F.3 (p. 51) gives.
--
--   **Difference:** the two differ only for $\delta$ near $1$. There the printed bounds fall below one step, while the variant's stay at least $\mathrm{poly}(\dots) \cdot \log 2$.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 13, Theorem 6.1 (corrected with p. 51, Lemma F.3)

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Empirical
import Definitions.Def_OptAbstention_TLA_Machine
import Definitions.Def_OptAbstention_TLA_Learner
open MeasureTheory

namespace OptAbstention.TLA

/-- Theorem 6.1, p. 13, with `log(2/δ)` in place of the printed `log(1/δ)`. Universal `C, k` come first; then for every
instance with `ℓ = L1(ε/2, B, C, D)` and `M_{D,ℓ} < ∞` there is one program that, on every run on
a test list of length `n ≥ 1`, draws at most `C·Z^k·log(1/δ)` samples and halts within
`C·(n Z)^k·log(1/δ)` steps, `Z = M_{D,ℓ}B(d+1)^ℓ/(εη)`, and is a
`(λ + opt_train + ε, η, δ)`-TLA learner for `C` with respect to `D`. -/
theorem theorem_6_1_log_two : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (d : ℕ) (X : Set (Pt d)) (D : Measure X) [IsProbabilityMeasure D] (Cl : Set (X → ℝ))
      (B ε η δ : ℝ) (ℓ : ℕ), IsConceptClass X Cl → 1 ≤ B → 0 < ε → ε < 1 → 0 < η → η < 1 →
      0 < δ → δ < 1 → IsL1Degree D (ε / 2) B Cl ℓ → momentBound D ℓ ≠ ⊤ →
      ∃ P : Program, Admissible P ∧
        (∀ (n : ℕ), 1 ≤ n → ∀ (xs : Fin n → X) (ξ : ExStream d), (∀ i, (ξ i).1 ∈ X) →
          ∀ ν : Tape,
          HaltsWithin P d ξ ν (testInit xs)
            (C * ((n : ℝ) * ((momentBound D ℓ).toReal * B * ((d : ℝ) + 1) ^ ℓ / (ε * η))) ^ k *
              Real.log (2 / δ))
            (C * ((momentBound D ℓ).toReal * B * ((d : ℝ) + 1) ^ ℓ / (ε * η)) ^ k *
              Real.log (2 / δ))) ∧
        IsTLALearner P D
          (fun Dbar _ xs ys => jointErr Dbar Cl xs ys + optTrain Dbar Cl + ENNReal.ofReal ε)
          η δ := by sorry

end OptAbstention.TLA
