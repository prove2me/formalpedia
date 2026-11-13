-- Prove2me | Theorems.Thm_MultiThinkCoT_lemma_A_5
-- name    : MultiThinkCoT.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:40:27.407288+00:00
-- url     : https://prove2.me/theorems/99a3c17a-f550-4919-97a8-1db87e5c4b21
-- title:
--   Lemma A.5 — $x\ge c(a\log^k a+b)\Rightarrow x\ge a\log^k x+b$
-- statement:
--   For every $k\ge1$ there is a constant $c>0$, depending only on $k$, such that for every $a\ge e$, every $b\ge0$ and every $x>0$,
--
--   $$
--   x\ \ge\ c\,\big(a\log^k(a)+b\big)\quad\Longrightarrow\quad x\ \ge\ a\log^k(x)+b .
--   $$
--
--   Theorem 7 uses it with $k=2$ to turn the implicit sample-size condition of Lemma F.4, in which $K=\lceil8\log(2m)\rceil$ depends on $m$, into the explicit $m(\varepsilon,\delta)$.
--
--   **Formalization Note** $\log^k u=(\log u)^k$ with the natural logarithm; $k$ is a real number $\ge1$ and the power is a real power.
--
--   Differences from the source:
--   - reading: for every k ≥ 1 (the paper does not say whether k is an integer) → every real k ≥ 1, log^k u = (log u)^k as a real power; reason: the more general of the two readings; it contains every integer k, in particular k = 2 used in Theorem 7
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix A, Lemma A.5, p.35 (PDF p.35)

import Mathlib

namespace MultiThinkCoT

/-- **Lemma A.5 (Algebraic inequality)**, p.35 (PDF p.35).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

For every `k ≥ 1` there exists a constant `c > 0`, depending only on `k`, such that for every
`a ≥ e`, every `b ≥ 0` and every `x > 0`: if `x ≥ c (a log^k(a) + b)` then
`x ≥ a log^k(x) + b`.

**Formalization Note.** `k` is a real number `≥ 1` (the paper does not say whether `k` is an
integer; Theorem 7 uses `k = 2`), and `log^k u = (log u)^k` is a real power (`Real.rpow`) of the
natural logarithm.
-/
theorem lemma_A_5 :
    ∀ k : ℝ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ a b x : ℝ, Real.exp 1 ≤ a → 0 ≤ b → 0 < x →
        c * (a * Real.log a ^ k + b) ≤ x → a * Real.log x ^ k + b ≤ x := by sorry

end MultiThinkCoT
