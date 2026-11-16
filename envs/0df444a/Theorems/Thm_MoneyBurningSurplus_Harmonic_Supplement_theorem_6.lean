-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_Supplement_theorem_6
-- name    : MoneyBurningSurplus.Harmonic.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:01:20.047303+00:00
-- url     : https://prove2.me/theorems/74a764fa-e614-45d5-b019-98ef3ab19185
-- title:
--   Theorem 6 — harmonic outcome sampling is UT, EPIR, nonnegative-payment with E[RS] ≥ W(N)/H_m, m = |O|
-- statement:
--   Let $n\ge2$ agents have arbitrary nonnegative valuations $v_i:O\to\mathbb R_{\ge0}$ on a nonempty finite outcome set $O$ with $m=|O|$ elements, and let $W(N)=\max_{o\in O}\sum_iv_i(o)$. The harmonic outcome-sampling mechanism draws $s\in\{1,\dots,m\}$ with probability $1/(sH_m)$ and a uniform $s$-subset $S_s\subseteq O$, chooses the tie-broken maximizer $o_{S_s}$ of $\sum_iv_i$ in $S_s$, and charges every agent
--
--   $$p_i(S_s)=\max_{o\in S_s}\sum_{j\ne i}v_j(o)-\sum_{j\ne i}v_j(o_{S_s}).$$
--
--   Then
--
--   1. for every $s$ and every range $S_s$, the resulting deterministic mechanism is truthful, ex-post individually rational and has nonnegative payments;
--   2. for every valuation profile,
--   $$\mathbb E\Big[\sum_{i\in N}\big(v_i(o_{S_s})-p_i(S_s)\big)\Big]\ge\frac{W(N)}{H_m}.$$
--
--   The factor depends on the number of outcomes rather than the number of agents; combined with Theorem 1 it gives the factor $H_{\min\{n,m\}}$.
--
--   **Formalization Note** The expectation is the finite average over $s$ and over the $s$-subsets of $O$; $H_m$ is Mathlib's `harmonic` at $m=$ `Fintype.card O`, cast to the reals.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n} with n ≥ 2, nonnegative valuations on a nonempty finite outcome set O → Fin n with 2 ≤ n, real-valued functions O → ℝ with pointwise nonnegativity carried by the domain, Fintype O, Nonempty O, DecidableEq O; reason: relabeling and decidable finite membership change no instance
--   - encoding: a fixed, report-independent tie-breaking rule among maximizing outcomes → a universally quantified tb : Finset O → O with IsTieBreak tb (it returns a member of every nonempty set), applied to the computed maximizer set; reason: the rule receives no reports; every instance of the paper's rule satisfies IsTieBreak
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, Theorem 6, PDF p. 26 (printed p. 25); harmonic outcome-sampling mechanism, App. D.1, PDF p. 26 (printed p. 25); proof PDF p. 27 (printed p. 26)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model
import Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Range

namespace MoneyBurningSurplus.Harmonic.Supplement

theorem theorem_6
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (tb : Finset O → O) (htb : IsTieBreak tb) :
    (∀ s ∈ Finset.Icc 1 (Fintype.card O),
      ∀ S ∈ (Finset.univ : Finset O).powersetCard s,
        AGT.MechIncentiveCompatible (valuationDomain (n := n))
            (rangeVCGOutcome tb S Finset.univ) (rangeVCGPay tb S Finset.univ) ∧
        AGT.IndividuallyRational (valuationDomain (n := n))
            (rangeVCGOutcome tb S Finset.univ) (rangeVCGPay tb S Finset.univ) ∧
        AGT.NoPositiveTransfers (valuationDomain (n := n))
            (rangeVCGOutcome tb S Finset.univ) (rangeVCGPay tb S Finset.univ)) ∧
    (∀ v : Fin n → O → ℝ, AGT.IsValProfile valuationDomain v →
      welfare v Finset.univ / (harmonic (Fintype.card O) : ℝ) ≤
        outcomeSamplingSurplus tb v) := by sorry

end MoneyBurningSurplus.Harmonic.Supplement
