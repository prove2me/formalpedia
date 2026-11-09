-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_theorem_1
-- name    : MoneyBurningSurplus.Harmonic.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:01.189931+00:00
-- url     : https://prove2.me/theorems/5f25ce22-d738-434d-be7b-793f85d7259a
-- title:
--   Theorem 1 — HASM is UT, EPIR, has nonnegative payments and guarantees W(N)/H_n
-- statement:
--   Let $N$ consist of $n\ge2$ agents and let $O$ be any nonempty finite outcome set. Every valuation $v_i:O\to\mathbb R_{\ge0}$ is admissible. Write $W(T)=\max_{o\in O}\sum_{i\in T}v_i(o)$ for $T\subseteq N$. Fix any report-independent tie-break rule. For a sampled set $R$, let $o_R$ maximize the sampled welfare using that rule, and let $p_i(R)$ be the Clarke-pivot payment computed on $R$, with zero payment outside $R$.
--
--   HASM chooses $k\in\{1,\ldots,n\}$ with probability $1/(kH_n)$, then a uniform $k$-subset $R$, independently of reports, where $H_n=\sum_{k=1}^n1/k$. For every such seed, its deterministic mechanism is truthful against every admissible unilateral deviation, every agent has nonnegative utility on every admissible profile, and every payment is nonnegative. For every valuation profile it also satisfies
--
--   $$\mathbb E\!\left[\sum_{i\in N}(v_i(o_R)-p_i(R))\right]\ge\frac{W(N)}{H_n}.$$
--
--   The expectation is only over HASM's internal randomness. This is the full pointwise prior-free guarantee, including universal truthfulness, ex-post individual rationality and nonnegative payments for sampled and unsampled agents alike.
--
--   **Formalization Note** The three per-seed guarantees use the published AGT incentive, individual-rationality and no-positive-transfer predicates on the full nonnegative domain. The finite expectation is computed from the exact sampling law and the true profile. Every valid pair $(k,R)$ is quantified, and every report-independent tie-break rule is covered.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n}, nonnegative valuations on a nonempty finite O → Fin n, real-valued functions in the full pointwise nonnegative domain, with Fintype O, Nonempty O and DecidableEq O; reason: relabeling and decidable finite membership change no instance; the standing assumption 2 ≤ n is retained
--   - encoding: a fixed report-independent tie-breaking rule for welfare maximizers → a universally quantified function on finite outcome sets satisfying IsTieBreak, applied to the computed maximizer set; reason: the rule receives no reports or unsampled information; its value on the empty set is never used for a maximization
--   - encoding: HASM expectation and harmonic number H_n → nested finite sums with weights 1/(k * (harmonic n : ℝ)) and inverse binomial counts; reason: these are exactly the two sampling stages; harmonic n has the same 1-through-n indexing
--   - encoding: universal truthfulness, ex-post individual rationality and nonnegative payments for every realization → the three AGT predicates on all agents for every k in Icc 1 n and R in powersetCard k univ; reason: each valid seed has positive mass; AGT quantifies over exactly the admissible profiles and deviations
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, Theorem 1 (Optimal prior-free surplus), PDF p. 8 (printed p. 7); proof PDF pp. 8–9 (printed pp. 7–8)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model

namespace MoneyBurningSurplus.Harmonic

theorem theorem_1
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (tb : Finset O → O) (htb : IsTieBreak tb) :
    (∀ k ∈ Finset.Icc 1 n,
      ∀ R ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        AGT.MechIncentiveCompatible valuationDomain (vcgOutcome tb R) (hasmPay tb R) ∧
        AGT.IndividuallyRational valuationDomain (vcgOutcome tb R) (hasmPay tb R) ∧
        AGT.NoPositiveTransfers valuationDomain (vcgOutcome tb R) (hasmPay tb R)) ∧
    (∀ v : Fin n → O → ℝ, AGT.IsValProfile valuationDomain v →
      welfare v Finset.univ / (harmonic n : ℝ) ≤ expectedResidualSurplus tb v) := by sorry

end MoneyBurningSurplus.Harmonic
