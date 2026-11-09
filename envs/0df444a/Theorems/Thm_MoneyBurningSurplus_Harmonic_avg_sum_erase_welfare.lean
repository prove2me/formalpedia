-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_avg_sum_erase_welfare
-- name    : MoneyBurningSurplus.Harmonic.avg_sum_erase_welfare
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:48.477206+00:00
-- url     : https://prove2.me/theorems/ac9d698e-96bd-4249-b7eb-6fa0c0b2ac7a
-- title:
--   §3, proof of Theorem 1 — random-subset deletion identity
-- statement:
--   Let $N$ consist of $n\ge2$ agents and let $O$ be any nonempty finite outcome set. Every valuation $v_i:O\to\mathbb R_{\ge0}$ is admissible. Write $W(T)=\max_{o\in O}\sum_{i\in T}v_i(o)$ for $T\subseteq N$.
--
--   Let $1\le k\le n$ and let $\overline W_j=\binom nj^{-1}\sum_{|T|=j}W(T)$ for $0\le j\le n$. Then
--
--   $$\binom nk^{-1}\sum_{|R|=k}\sum_{i\in R}W(R\setminus\{i\})=k\overline W_{k-1}.$$
--
--   This is the displayed expectation after “Multiplying by k” in the source. It relates welfare averages at adjacent sample sizes.
--
--   **Formalization Note** Expectations are exact finite averages. The explicit bounds on $k$ preserve the full source range, including $k=1$ and $k=n$.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n}, nonnegative valuations on a nonempty finite O → Fin n, real-valued functions in the full pointwise nonnegative domain, with Fintype O, Nonempty O and DecidableEq O; reason: relabeling and decidable finite membership change no instance; the standing assumption 2 ≤ n is retained
--   - encoding: expectation over a uniform k-subset → a finite sum divided by Nat.choose n k, with 1 ≤ k ≤ n and predecessor k - 1; reason: the denominator is positive and predecessor subtraction is exact throughout the source range
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, §3, proof of Theorem 1, random-subset identity, display after “Multiplying by k”, PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model

namespace MoneyBurningSurplus.Harmonic

theorem avg_sum_erase_welfare
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (v : Fin n → O → ℝ) (hv : AGT.IsValProfile valuationDomain v)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (Nat.choose n k : ℝ)⁻¹ *
      (∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∑ i ∈ R, welfare v (R.erase i)) =
      (k : ℝ) * avgWelfare v (k - 1) := by sorry

end MoneyBurningSurplus.Harmonic
