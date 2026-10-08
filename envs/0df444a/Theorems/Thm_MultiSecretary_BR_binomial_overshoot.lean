-- Prove2me | Theorems.Thm_MultiSecretary_BR_binomial_overshoot
-- name    : MultiSecretary.BR.binomial_overshoot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:37:32.392456+00:00
-- url     : https://prove2.me/theorems/d86515fa-f6e0-448c-aaf1-86d74692c0f2
-- title:
--   Lemma 2 — $\mathbb E[(B-k)_+]\le 1/(4\varepsilon)$ if $(p+\varepsilon)n\le k$, and $\mathbb E[(k-B)_+]\le 1/(4\varepsilon)$ if $k\le(p-\varepsilon)n$
-- statement:
--   Let $B$ be a binomial random variable with $n$ trials and success probability $p\in[0,1]$, let $k\in\mathbb Z_+$ and $\varepsilon>0$. Then
--   $$\mathbb E[(B-k)_+]\le\frac1{4\varepsilon}\quad\text{if }(p+\varepsilon)n\le k,\qquad\text{and}\qquad\mathbb E[(k-B)_+]\le\frac1{4\varepsilon}\quad\text{if }k\le(p-\varepsilon)n.$$
--
--   When the budget $k$ exceeds the mean $pn$ by a linear margin, the expected overshoot of $B$ beyond $k$ is bounded by a constant independent of $n$, and symmetrically for the undershoot. The paper uses this repeatedly, first in Proposition 1.
--
--   **Formalization Note** $B$ is the number of successes of $b\in\{0,1\}^n$ under the product weight $\prod_t(p\text{ if }b_t=1\text{, else }1-p)$; expectations are finite sums. The page states the conditions as $p+\varepsilon\le k/n$ and $k/n\le p-\varepsilon$. They are written here in the multiplied form used by the proof (Appendix B, p. 32), which is equivalent for $n\ge1$; with Lean's convention $k/0=0$ the printed second condition would hold at $n=0$ for every $k$ and the bound would fail (e.g. $k=100$, $p=1$, $\varepsilon=\tfrac12$).
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Lemma 2, p. 8; proof in Appendix B, p. 32

import Mathlib

namespace MultiSecretary.BR

open Finset

/-- Lemma 2, p. 8 (proof in Appendix B, p. 32). Let `B` be binomial with `n` trials and success
probability `p`, realized as the number of successes of `b : Fin n → Bool` under the product weight
`∏_t (p if b t else 1 − p)`. For every `ε > 0`:
`E[(B − k)_+] ≤ 1/(4ε)` if `(p + ε) n ≤ k`, and `E[(k − B)_+] ≤ 1/(4ε)` if `k ≤ (p − ε) n`.
(The page writes the conditions as `p + ε ≤ k/n` and `k/n ≤ p − ε`; the multiplied form is the one
the proof uses and also covers `n = 0`.) -/
theorem binomial_overshoot (n k : ℕ) (p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) :
    ((p + ε) * n ≤ k →
      ∑ b : Fin n → Bool, (∏ t, if b t = true then p else 1 - p) *
        max (((univ.filter (fun t => b t = true)).card : ℝ) - k) 0 ≤ 1 / (4 * ε)) ∧
    ((k : ℝ) ≤ (p - ε) * n →
      ∑ b : Fin n → Bool, (∏ t, if b t = true then p else 1 - p) *
        max ((k : ℝ) - (univ.filter (fun t => b t = true)).card) 0 ≤ 1 / (4 * ε)) := by sorry

end MultiSecretary.BR
