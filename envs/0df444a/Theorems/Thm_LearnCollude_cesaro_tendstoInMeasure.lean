-- Prove2me | Theorems.Thm_LearnCollude_cesaro_tendstoInMeasure
-- name    : LearnCollude.cesaro_tendstoInMeasure
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:38.88992+00:00
-- url     : https://prove2.me/theorems/abbc6929-d2b3-40f9-88ea-cb5e2854ccd6
-- title:
--   (96)–(98) — Cesàro means of a bounded sequence converging in probability
-- statement:
--   Let $X_1,X_2,\dots$ be random variables on a probability space with $|X_n|\le B$ for all $n$, and $X_n\to0$ in probability. Then
--   $$
--   \frac1n\sum_{k=1}^nX_k\to0\quad\text{in probability.}
--   $$
--   This step passes from the convergence of the phase-5 prices to the convergence of the time-average prices.
--
--   Differences from the source:
--   - generalization: (96)–(98) for the sequence χ(n) → any uniformly bounded sequence of random variables converging to 0 in probability; reason: χ(n) is such a sequence; the printed derivation is circular in n₀ and n₁, and the statement is right
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), eqs. (96)–(98), p. 47

import Mathlib

open Filter MeasureTheory

namespace LearnCollude

/-- **Cesàro means of a bounded sequence converging in probability**, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), eqs. (96)–(98), p. 47.

If the random variables `Xₙ` are uniformly bounded and `Xₙ → 0` in probability, then
`(1/n) Σ_{k ≤ n} X_k → 0` in probability.

**Formalization Note** The paper derives this for its sequence `χ(n)`, and the printed derivation
chooses `n₀` from `n₁` and `n₁` from `n₀`. The statement is the general form. -/
theorem cesaro_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (B : ℝ) (hX : ∀ n, Measurable (X n))
    (hB : ∀ n x, |X n x| ≤ B) (hlim : TendstoInMeasure μ X atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun (n : ℕ) x => (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, X k x) atTop
      (fun _ => 0) := by sorry

end LearnCollude
