-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_vcg_utility_eq
-- name    : MoneyBurningSurplus.Harmonic.vcg_utility_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:46.774198+00:00
-- url     : https://prove2.me/theorems/a29d87a7-481c-4f50-b4e1-50943662206f
-- title:
--   §3, proof of Theorem 1 — sampled-VCG utility identity
-- statement:
--   Let $N$ consist of $n\ge2$ agents and let $O$ be any nonempty finite outcome set. Every valuation $v_i:O\to\mathbb R_{\ge0}$ is admissible. Write $W(T)=\max_{o\in O}\sum_{i\in T}v_i(o)$ for $T\subseteq N$. Fix any report-independent tie-break rule. For a sampled set $R$, let $o_R$ maximize the sampled welfare using that rule, and let $p_i(R)$ be the Clarke-pivot payment computed on $R$, with zero payment outside $R$.
--
--   For every $R\subseteq N$ and every $i\in R$,
--
--   $$v_i(o_R)-p_i(R)=W(R)-W(R\setminus\{i\}).$$
--
--   This identifies sampled-agent utility with its welfare marginal, the quantity used in the surplus analysis.
--
--   **Formalization Note** The sampled set is arbitrary; membership of $i$ is an explicit hypothesis, and welfare and payments are computed rather than assumed.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n}, nonnegative valuations on a nonempty finite O → Fin n, real-valued functions in the full pointwise nonnegative domain, with Fintype O, Nonempty O and DecidableEq O; reason: relabeling and decidable finite membership change no instance; the standing assumption 2 ≤ n is retained
--   - encoding: a fixed report-independent tie-breaking rule for welfare maximizers → a universally quantified function on finite outcome sets satisfying IsTieBreak, applied to the computed maximizer set; reason: the rule receives no reports or unsampled information; its value on the empty set is never used for a maximization
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, §3, proof of Theorem 1, sampled-VCG utility identity, PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model

namespace MoneyBurningSurplus.Harmonic

theorem vcg_utility_eq
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (tb : Finset O → O) (htb : IsTieBreak tb)
    (v : Fin n → O → ℝ) (hv : AGT.IsValProfile valuationDomain v)
    (R : Finset (Fin n)) (i : Fin n) (hi : i ∈ R) :
    v i (vcgOutcome tb R v) - hasmPay tb R i v =
      welfare v R - welfare v (R.erase i) := by sorry

end MoneyBurningSurplus.Harmonic
