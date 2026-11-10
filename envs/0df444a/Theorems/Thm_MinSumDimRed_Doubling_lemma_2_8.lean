-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_lemma_2_8
-- name    : MinSumDimRed.Doubling.lemma_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:35:59.144819+00:00
-- url     : https://prove2.me/theorems/d61043b3-db13-4b26-b3f3-df5ee6670917
-- title:
--   Lemma 2.8 — Gaussian local ball-tail in doubling sets: $t \ge c(\mathrm{ddim} + \mu)$ gives the $\mu$-local ball-tail property
-- statement:
--   **Lemma 2.8** (Gaussian Local Ball-Tail in Doubling Sets [IN07], p. 10). There is a universal constant $c > 0$ such that for every $d$, every $X \subseteq \mathbb R^d$ (not necessarily finite) of doubling dimension at most $\mathrm{ddim} \ge 1$, every real $\mu$ and every $t$ with $t \ge c(\mathrm{ddim} + \mu)$, the Gaussian JL map $f : \mathbb R^d \to \mathbb R^t$ has the $\mu$-local ball-tail property for $X$: for every $y \in X$ and $r > 0$,
--   $$\Pr\big[\exists x \in X \cap B(y, r),\ \|f(x) - f(y)\| \ge 10 r\big] \le e^{-\mu}.$$
--
--   Differences from the source:
--   - reading: universal constant c → explicit existential constants (∃ … > 0) quantified before every instance parameter; reason: the source asserts a single universal constant before all instance parameters; when D + µ is positive a larger constant strengthens the dimension hypothesis, and when D + µ is nonpositive, µ ≤ -1 makes the tail bound automatic
--   - encoding: X has doubling dimension at most ddim ≥ 1 → 1 ≤ D ∧ HasDoublingDimAtMost X D (some admissible exponent D' ≤ D); reason: equivalent to ddim(X) ≤ D because the infimum of admissible exponents is attained, and never satisfied by a non-doubling X
--   - encoding: Gaussian JL map f : ℝ^d → ℝ^t, a matrix with independent N(0, 1/t) entries → W drawn from gaussianJLLaw t d = UnderstandingML.gaussianMatrixLaw t d (t : NNReal)⁻¹ (entries gaussianReal 0 (1/t), second argument the variance), f = jlMap W, x ↦ W x; reason: the published product Gaussian law; 1/t is the variance as in N(0, 1/t)
--   - encoding: B(y, r) → closed ball: dist x y ≤ r; reason: the paper's balls are closed (p. 9)
--   - encoding: target dimension t → t : ℕ, with the hypothesis on (t : ℝ); reason: dimensions are natural numbers
--   - encoding: with probability at least p / Pr[event] ≤ q → p ≤ μ.real {ω | …} / μ.real {ω | …} ≤ q on a probability measure μ; reason: μ.real is the (outer) measure as a real number; no measurability of the event is presupposed, and for measurable events it is the probability
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 10 (PDF 10), Lemma 2.8

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_MinSumDimRed_Doubling_Random

open MeasureTheory ProbabilityTheory

namespace MinSumDimRed.Doubling

/-- Lemma 2.8 (Gaussian Local Ball-Tail in Doubling Sets [IN07]), p. 10: there is a universal
constant `c > 0` such that if `X ⊆ ℝ^d` has doubling dimension at most `ddim ≥ 1` and `f` is a
Gaussian JL map `ℝ^d → ℝ^t` with `t ≥ c (ddim + µ)`, then `f` has the `µ`-local ball-tail
property for `X`. `X` is an arbitrary (not necessarily finite) subset. -/
theorem lemma_2_8 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (X : Set (Pt d)) (D : ℝ), 1 ≤ D → HasDoublingDimAtMost X D →
      ∀ (mu : ℝ) (t : ℕ), c * (D + mu) ≤ (t : ℝ) →
        HasLocalBallTail (gaussianJLLaw t d) (fun W => jlMap W) X mu := by sorry

end MinSumDimRed.Doubling
