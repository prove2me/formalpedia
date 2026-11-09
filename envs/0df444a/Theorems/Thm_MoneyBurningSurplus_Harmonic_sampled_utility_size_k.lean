-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_sampled_utility_size_k
-- name    : MoneyBurningSurplus.Harmonic.sampled_utility_size_k
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:46.573182+00:00
-- url     : https://prove2.me/theorems/a12b113d-a9a1-4423-af6d-bbde5760874c
-- title:
--   §3, proof of Theorem 1 — sampled utility conditional on size k
-- statement:
--   Let $N$ consist of $n\ge2$ agents and let $O$ be any nonempty finite outcome set. Every valuation $v_i:O\to\mathbb R_{\ge0}$ is admissible. Write $W(T)=\max_{o\in O}\sum_{i\in T}v_i(o)$ for $T\subseteq N$. Fix any report-independent tie-break rule. For a sampled set $R$, let $o_R$ maximize the sampled welfare using that rule, and let $p_i(R)$ be the Clarke-pivot payment computed on $R$, with zero payment outside $R$.
--
--   For $1\le k\le n$, put $\overline W_j=\binom nj^{-1}\sum_{|T|=j}W(T)$ and $C_k=\binom nk^{-1}\sum_{|R|=k}\sum_{i\in R}(v_i(o_R)-p_i(R))$. Then
--
--   $$C_k=k(\overline W_k-\overline W_{k-1}).$$
--
--   This gives the exact conditional sampled utility that enters HASM's harmonic mixture.
--
--   **Formalization Note** Both averages are definitions from the same profile and mechanism; neither is an arbitrary variable constrained by a hypothesis.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n}, nonnegative valuations on a nonempty finite O → Fin n, real-valued functions in the full pointwise nonnegative domain, with Fintype O, Nonempty O and DecidableEq O; reason: relabeling and decidable finite membership change no instance; the standing assumption 2 ≤ n is retained
--   - encoding: a fixed report-independent tie-breaking rule for welfare maximizers → a universally quantified function on finite outcome sets satisfying IsTieBreak, applied to the computed maximizer set; reason: the rule receives no reports or unsampled information; its value on the empty set is never used for a maximization
--   - encoding: expectation over a uniform k-subset → a finite sum divided by Nat.choose n k, with 1 ≤ k ≤ n and predecessor k - 1; reason: the denominator is positive and predecessor subtraction is exact throughout the source range
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, §3, proof of Theorem 1, display C_k = k(average W_k − average W_(k−1)), PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model

namespace MoneyBurningSurplus.Harmonic

theorem sampled_utility_size_k
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (tb : Finset O → O) (htb : IsTieBreak tb)
    (v : Fin n → O → ℝ) (hv : AGT.IsValProfile valuationDomain v)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    sampledUtility tb v k = (k : ℝ) * (avgWelfare v k - avgWelfare v (k - 1)) := by sorry

end MoneyBurningSurplus.Harmonic
