-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_Supplement_theorem_4
-- name    : MoneyBurningSurplus.Harmonic.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:58:33.053335+00:00
-- url     : https://prove2.me/theorems/086c0387-0f87-4970-81c8-09dbf484e7df
-- title:
--   Theorem 4 — harmonic MIR sampling over a fixed range R is UT, EPIR with E[RS] ≥ W_R(N)/H_n, hence αH_n for an α-approximate range
-- statement:
--   Let $n\ge2$ agents have valuations in domains $V_i$ of nonnegative valuations on a nonempty finite outcome set $O$, and let $R\subseteq O$ be a nonempty fixed range. Write $W_R(T)=\max_{o\in R}\sum_{i\in T}v_i(o)$ and $W(N)=\max_{o\in O}\sum_iv_i(o)$. The harmonic MIR mechanism draws $k\in\{1,\dots,n\}$ with probability $1/(kH_n)$ and a uniform $k$-subset $R_k$ of agents, chooses the tie-broken maximizer $o$ of $\sum_{i\in R_k}v_i$ within $R$, charges $i\in R_k$ the pivot $W_R(R_k\setminus\{i\})-\sum_{j\in R_k\setminus\{i\}}v_j(o)$ and everyone else $0$. Then
--
--   1. for every $k$ and every sampled set $R_k$, the resulting deterministic mechanism is truthful, ex-post individually rational and has nonnegative payments on the domains;
--   2. for every admissible profile,
--   $$\mathbb E[RS]=\mathbb E\Big[\sum_{i\in N}\big(v_i(o)-p_i\big)\Big]\ge\frac{W_R(N)}{H_n};$$
--   3. consequently, for every $\alpha>0$, if $W_R(N)\ge W(N)/\alpha$ at every admissible profile, then $\mathbb E[RS]\ge W(N)/(\alpha H_n)$ at every admissible profile.
--
--   With $R=O$ this is Theorem 1; for a proper range it lets maximal-in-range approximation algorithms be used in place of exact welfare maximization.
--
--   **Formalization Note** The expectation is the finite average over $k$ and over the $k$-subsets. The range and the tie-break rule are fixed and report-independent; agents outside the sampled set are ignored and pay $0$.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n} with n ≥ 2, nonnegative valuations on a nonempty finite outcome set O → Fin n with 2 ≤ n, real-valued functions O → ℝ with pointwise nonnegativity carried by the domain, Fintype O, Nonempty O, DecidableEq O; reason: relabeling and decidable finite membership change no instance
--   - encoding: a fixed, report-independent tie-breaking rule among maximizing outcomes → a universally quantified tb : Finset O → O with IsTieBreak tb (it returns a member of every nonempty set), applied to the computed maximizer set; reason: the rule receives no reports; every instance of the paper's rule satisfies IsTieBreak
--   - generalization: every valuation profile (by default all nonnegative valuations) → every profile in arbitrary domains V i of nonnegative valuations, reports and deviations in V; reason: specializes to V = valuationDomain, the paper's default
--   - reading: the harmonic MIR mechanism is universally truthful and ex-post individually rational → the same, plus nonnegative payments, for every seed (k, R_k) with 1 ≤ k ≤ n; reason: §2 requires every mechanism's payments to lie in ℝ≥0, and the Clarke pivot over R is nonnegative
--   - generalization: R is an α-approximate range (α an approximation factor, α ≥ 1 by §2) → every real α > 0; reason: covers every α ≥ 1; for α < 1 the hypothesis forces W(N) = 0
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, Theorem 4, PDF p. 18 (printed p. 17); App. B.1 definition of W_R and of the harmonic MIR mechanism, PDF p. 18 (printed p. 17); fixed master range, App. B intro, PDF p. 18

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model
import Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Range

namespace MoneyBurningSurplus.Harmonic.Supplement

theorem theorem_4
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (tb : Finset O → O) (htb : IsTieBreak tb)
    (R : Finset O) (hR : R.Nonempty)
    (V : Fin n → Set (O → ℝ)) (hV : ∀ i, ∀ u ∈ V i, ∀ o, 0 ≤ u o) :
    (∀ k ∈ Finset.Icc 1 n,
      ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        AGT.MechIncentiveCompatible V (rangeVCGOutcome tb R T) (rangeVCGPay tb R T) ∧
        AGT.IndividuallyRational V (rangeVCGOutcome tb R T) (rangeVCGPay tb R T) ∧
        AGT.NoPositiveTransfers V (rangeVCGOutcome tb R T) (rangeVCGPay tb R T)) ∧
    (∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
      rangeWelfare R v Finset.univ / (harmonic n : ℝ) ≤ mirSurplus tb R v) ∧
    (∀ α : ℝ, 0 < α →
      (∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
        welfare v Finset.univ / α ≤ rangeWelfare R v Finset.univ) →
      ∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
        welfare v Finset.univ / (α * (harmonic n : ℝ)) ≤ mirSurplus tb R v) := by sorry

end MoneyBurningSurplus.Harmonic.Supplement
