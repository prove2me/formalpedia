-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_lemma_2_5
-- name    : MinSumDimRed.Doubling.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:35:33.995198+00:00
-- url     : https://prove2.me/theorems/e7b50085-93f3-42f7-a493-574870dfb79a
-- title:
--   Lemma 2.5 — Gaussian pair tail: $t \ge c\varepsilon^{-2}\log(1/\delta)$ gives $\Pr[\|f(x)-f(y)\| \notin (1\pm\varepsilon)\|x-y\|] \le \delta$
-- statement:
--   **Lemma 2.5** (Gaussian Pair Tail [Mat08, Theorem 3.1], p. 10). There is a universal constant $c > 0$ such that for every $0 < \varepsilon, \delta < 1$, every $d$ and every $t$ with $t \ge c\,\varepsilon^{-2} \log(1/\delta)$, the Gaussian JL map $f(x) = Wx$ ($W$ a $t \times d$ matrix with independent $N(0, 1/t)$ entries) satisfies, for every fixed $x, y \in \mathbb R^d$,
--   $$\Pr\big[\|f(x) - f(y)\| \notin (1 \pm \varepsilon)\|x - y\|\big] \le \delta.$$
--
--   Differences from the source:
--   - reading: universal constant c → explicit existential constants (∃ … > 0) quantified before every instance parameter; reason: one universal constant; since every hypothesis containing it gets stronger as it grows, 'sufficiently large' is equivalent to 'some'
--   - encoding: Gaussian JL map f : ℝ^d → ℝ^t, a matrix with independent N(0, 1/t) entries → W drawn from gaussianJLLaw t d = UnderstandingML.gaussianMatrixLaw t d (t : NNReal)⁻¹ (entries gaussianReal 0 (1/t), second argument the variance), f = jlMap W, x ↦ W x; reason: the published product Gaussian law; 1/t is the variance as in N(0, 1/t)
--   - reading: a ∈ (1 ± ε) b → WithinFactor ε a b, i.e. (1 − ε)·b ≤ a ∧ a ≤ (1 + ε)·b (closed interval); reason: the paper does not say open or closed; the closed interval is the standard meaning and both inequalities are kept
--   - reading: log (base unspecified) → Real.log (natural logarithm); reason: any fixed base only rescales the absolute constants, which are existentially quantified
--   - encoding: target dimension t → t : ℕ, with the hypothesis on (t : ℝ); reason: dimensions are natural numbers
--   - encoding: with probability at least p / Pr[event] ≤ q → p ≤ μ.real {ω | …} / μ.real {ω | …} ≤ q on a probability measure μ; reason: μ.real is the (outer) measure as a real number; no measurability of the event is presupposed, and for measurable events it is the probability
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 10 (PDF 10), Lemma 2.5

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Random

open MeasureTheory ProbabilityTheory

namespace MinSumDimRed.Doubling

/-- Lemma 2.5 (Gaussian Pair Tail [Mat08, Theorem 3.1]), p. 10: there is a universal constant
`c > 0` such that for every `0 < ε, δ < 1`, a Gaussian JL map `f : ℝ^d → ℝ^t` with
`t ≥ c ε^{-2} log(1/δ)` satisfies, for every fixed `x, y ∈ ℝ^d`,
`Pr[‖f(x) - f(y)‖ ∉ (1 ± ε)‖x - y‖] ≤ δ`. -/
theorem lemma_2_5 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ (d t : ℕ), c * (ε ^ 2)⁻¹ * Real.log (1 / δ) ≤ (t : ℝ) →
      ∀ x y : Pt d,
        (gaussianJLLaw t d).real
            {W | ¬ WithinFactor ε ‖jlMap W x - jlMap W y‖ ‖x - y‖} ≤ δ := by sorry

end MinSumDimRed.Doubling
