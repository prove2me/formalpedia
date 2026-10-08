-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_binomial_overshoot
-- name    : MultiSecretary.NonAdaptive.binomial_overshoot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:43:07.216467+00:00
-- url     : https://prove2.me/theorems/29a036a2-79bc-4cb4-8e75-5ea3ceaa0922
-- title:
--   Lemma 2 — E[(B − k)₊] ≤ 1/(4ε) if (p + ε)n ≤ k, and E[(k − B)₊] ≤ 1/(4ε) if k ≤ (p − ε)n
-- statement:
--   Let $B$ be a binomial random variable with $n$ trials and success probability $p\in[0,1]$, let $k\ge0$ be an integer and $\varepsilon>0$. Then
--   $$\mathbb E[(B-k)_+]\le\frac1{4\varepsilon}\quad\text{if }(p+\varepsilon)n\le k,\qquad \mathbb E[(k-B)_+]\le\frac1{4\varepsilon}\quad\text{if }k\le(p-\varepsilon)n.$$
--
--   The overshoot of a binomial beyond a level a constant fraction above (or below) its mean is bounded uniformly in $n$. It is used repeatedly: for Lemma 4, Proposition 6 and the proof of Theorem 3.
--
--   **Formalization Note** The expectations are written with the binomial probability mass function. The paper states the conditions as $p+\varepsilon\le k/n$ and $k/n\le p-\varepsilon$; they are stated in the multiplied form its proof uses (p. 32), which agrees for $n\ge1$ and avoids $k/0=0$ in Lean.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Lemma 2, eq. (8), p. 8 (proof p. 32)

import Mathlib

namespace MultiSecretary.NonAdaptive

open Finset

/-- Lemma 2 (p. 8): for `B ~ Binomial(n, p)` and `ε > 0`,
`E[(B - k)_+] ≤ 1/(4ε)` if `(p + ε) n ≤ k`, and `E[(k - B)_+] ≤ 1/(4ε)` if `k ≤ (p - ε) n`. -/
theorem binomial_overshoot (n k : ℕ) (p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) :
    ((p + ε) * n ≤ k →
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) *
        max ((i : ℝ) - k) 0 ≤ 1 / (4 * ε)) ∧
    ((k : ℝ) ≤ (p - ε) * n →
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) *
        max ((k : ℝ) - i) 0 ≤ 1 / (4 * ε)) := by sorry

end MultiSecretary.NonAdaptive
