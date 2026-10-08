-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_lemma_1
-- name    : GenCMu.HeavyTraffic.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:10.62007+00:00
-- url     : https://prove2.me/theorems/44ef561d-e14f-4f86-b129-de1879e85750
-- title:
--   Lemma 1 — the largest jump of a partial-sums process with a continuous diffusion expansion is $o(n^{1/2})$
-- statement:
--   Fix $a > 0$. For each $n$ let $x^n_1, x^n_2, \dots \ge 0$ with partial sums $X^n(j) = \sum_{i=1}^{\lfloor j\rfloor} x^n_i$. Suppose there are functions $\bar X^n, \tilde X^n$, continuous on $[0,a]$, with the $\bar X^n$ sharing a finite Lipschitz bound, and converging uniformly on $[0,a]$ to continuous $\bar X^*, \tilde X^*$, such that uniformly in $s \in [0,a]$
--   $$X^n(ns) = n\bar X^n(s) + n^{1/2}\tilde X^n(s) + o(n^{1/2}).$$
--   Then
--   $$n^{-1/2}\max_{1\le i\le \lfloor na\rfloor} x^n_i \to 0.$$
--
--   Applied to the interarrival times and the service times it gives (33)–(34) of Proposition 2.
--
--   **Formalization Note** The paper states the lemma as "If $\bar U^*_k, \tilde U^*_k \in \mathcal C$, then $n^{-1/2}\sup_{1\le i\le A^n(n\cdot)}u^n_{k,i} \to 0$", with the convergences $\bar U^n\to\bar U^*$, $\tilde U^n\to\tilde U^*$ and the expansion (23) implicit; we state it for a generic partial-sums process with those hypotheses explicit. The common Lipschitz bound is an additional correction: uniform convergence of $\bar X^n$ alone permits jumps of order $\sqrt n$ in the partial sums. The index range $\lfloor na\rfloor$ stands for $A^n(n)$.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), Appendix, p. 828, Lemma 1

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Lemma 1 (Van Mieghem 1995, p. 828), with the hypotheses made explicit: nonnegative jumps
`x n i` (`i ≥ 1`) whose partial sums `Xⁿ` admit, uniformly on `[0, a]`, the expansion
`Xⁿ(ns) = nX̄ⁿ(s) + n^{1/2}X̃ⁿ(s) + o(n^{1/2})` with continuous terms converging uniformly to continuous
limits `X̄*`, `X̃*`. Then the largest jump among the first `⌊na⌋` is `o(n^{1/2})`. -/
theorem lemma_1 (a : ℝ) (ha : 0 < a) (x : ℕ → ℕ → ℝ) (hx : ∀ n i, 0 ≤ x n i)
    (Xbar Xtil : ℕ → ℝ → ℝ) (Xbs Xts : ℝ → ℝ)
    (hXbar : ∀ n, ContinuousOn (Xbar n) (Set.Icc 0 a))
    (hbar_lipschitz : ∃ B : ℝ, 0 ≤ B ∧ ∀ n s t, s ∈ Set.Icc (0 : ℝ) a →
      t ∈ Set.Icc (0 : ℝ) a → |Xbar n s - Xbar n t| ≤ B * |s - t|)
    (hXtil : ∀ n, ContinuousOn (Xtil n) (Set.Icc 0 a))
    (hXbs : ContinuousOn Xbs (Set.Icc 0 a)) (hXts : ContinuousOn Xts (Set.Icc 0 a))
    (hbar : TendstoUniformlyOn Xbar Xbs atTop (Set.Icc 0 a))
    (htil : TendstoUniformlyOn Xtil Xts atTop (Set.Icc 0 a))
    (hexp : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) a,
      |partialSum (x n) ⌊(n : ℝ) * s⌋₊ - (n * Xbar n s + Real.sqrt n * Xtil n s)|
        ≤ ε * Real.sqrt n) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.Icc 1 ⌊(n : ℝ) * a⌋₊, x n i ≤ ε * Real.sqrt n := by sorry
end GenCMu.HeavyTraffic
