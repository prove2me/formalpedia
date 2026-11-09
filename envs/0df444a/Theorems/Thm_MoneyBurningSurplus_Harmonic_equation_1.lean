-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_equation_1
-- name    : MoneyBurningSurplus.Harmonic.equation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:59.749665+00:00
-- url     : https://prove2.me/theorems/db86d537-45f4-484d-8fcf-ef484149f875
-- title:
--   §3, proof of Theorem 1, Equation (1) — exact expected sampled utility
-- statement:
--   Let $N$ consist of $n\ge2$ agents and let $O$ be any nonempty finite outcome set. Every valuation $v_i:O\to\mathbb R_{\ge0}$ is admissible. Write $W(T)=\max_{o\in O}\sum_{i\in T}v_i(o)$ for $T\subseteq N$. Fix any report-independent tie-break rule. For a sampled set $R$, let $o_R$ maximize the sampled welfare using that rule, and let $p_i(R)$ be the Clarke-pivot payment computed on $R$, with zero payment outside $R$.
--
--   Let $C_k=\binom nk^{-1}\sum_{|R|=k}\sum_{i\in R}(v_i(o_R)-p_i(R))$ and $H_n=\sum_{k=1}^n1/k$. Under HASM's sampling probabilities,
--
--   $$\sum_{k=1}^n\frac{C_k}{kH_n}=\frac{W(N)}{H_n}.$$
--
--   This is the exact expected total utility of sampled agents. It is an equality; unsampled agents' values enter the final residual-surplus bound separately.
--
--   **Formalization Note** The sum is over the closed integer interval from one through $n$ and uses the mechanism's defined size probabilities.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n}, nonnegative valuations on a nonempty finite O → Fin n, real-valued functions in the full pointwise nonnegative domain, with Fintype O, Nonempty O and DecidableEq O; reason: relabeling and decidable finite membership change no instance; the standing assumption 2 ≤ n is retained
--   - encoding: a fixed report-independent tie-breaking rule for welfare maximizers → a universally quantified function on finite outcome sets satisfying IsTieBreak, applied to the computed maximizer set; reason: the rule receives no reports or unsampled information; its value on the empty set is never used for a maximization
--   - encoding: HASM expectation and harmonic number H_n → nested finite sums with weights 1/(k * (harmonic n : ℝ)) and inverse binomial counts; reason: these are exactly the two sampling stages; harmonic n has the same 1-through-n indexing
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, §3, proof of Theorem 1, Equation (1), PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model

namespace MoneyBurningSurplus.Harmonic

theorem equation_1
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (tb : Finset O → O) (htb : IsTieBreak tb)
    (v : Fin n → O → ℝ) (hv : AGT.IsValProfile valuationDomain v)
    : (∑ k ∈ Finset.Icc 1 n, hasmProb n k * sampledUtility tb v k) =
      welfare v Finset.univ / (harmonic n : ℝ) := by sorry

end MoneyBurningSurplus.Harmonic
