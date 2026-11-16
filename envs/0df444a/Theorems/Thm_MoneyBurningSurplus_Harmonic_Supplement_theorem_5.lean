-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_Supplement_theorem_5
-- name    : MoneyBurningSurplus.Harmonic.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:59:57.826541+00:00
-- url     : https://prove2.me/theorems/2ffd91bd-89f9-4e06-b49e-722c4c53ed93
-- title:
--   Theorem 5 — harmonic MIDR sampling is TIE, EPIR with E[RS] ≥ W_D(N)/H_n, hence αH_n for an α-approximate distributional range
-- statement:
--   Let $n\ge2$ agents have valuations in domains $V_i$ of nonnegative valuations on a nonempty finite outcome set $O$. Let $\mathcal D$ be a nonempty fixed collection of probability distributions on $O$ such that, for every admissible profile and every set of agents $T$, the maximum
--
--   $$W_{\mathcal D}(T)=\max_{D\in\mathcal D}\mathbb E_{o\sim D}\Big[\sum_{i\in T}v_i(o)\Big]$$
--
--   is attained. Fix a rule choosing a member of every nonempty set of distributions. The harmonic MIDR mechanism draws $k\in\{1,\dots,n\}$ with probability $1/(kH_n)$ and a uniform $k$-subset $R_k$, selects the tie-broken maximizing distribution $D_{R_k}$, draws $o\sim D_{R_k}$, and charges $i\in R_k$
--
--   $$p_i(o;R_k)=\begin{cases}p_i(R_k)\,v_i(o)/a_i(R_k),&a_i(R_k)>0,\\0,&a_i(R_k)=0,\end{cases}$$
--
--   where $a_i(R_k)=\mathbb E_{o\sim D_{R_k}}[v_i(o)]$ and $p_i(R_k)=W_{\mathcal D}(R_k\setminus\{i\})-\mathbb E_{o\sim D_{R_k}}\big[\sum_{j\in R_k\setminus\{i\}}v_j(o)\big]$, all computed from reports; agents outside $R_k$ pay $0$. Then
--
--   1. the mechanism is truthful in expectation: for every admissible profile $v$, agent $i$ and $\tilde v_i\in V_i$, agent $i$'s expected utility $\mathbb E[v_i(o)-p_i]$ (over $k$, $R_k$ and $o$, with her true $v_i$) at $v$ is at least that at $(\tilde v_i,v_{-i})$;
--   2. it is ex-post individually rational: at every admissible profile, every seed $(k,R_k)$ and every outcome $o$, every agent has $v_i(o)-p_i(o;R_k)\ge0$;
--   3. every such payment is nonnegative;
--   4. for every admissible profile, $\mathbb E[RS]\ge W_{\mathcal D}(N)/H_n$, the expectation over the harmonic sampling and $o\sim D_{R_k}$;
--   5. consequently, for every $\alpha>0$, if $W_{\mathcal D}(N)\ge W(N)/\alpha$ at every admissible profile, then $\mathbb E[RS]\ge W(N)/(\alpha H_n)$ at every admissible profile.
--
--   This extends harmonic sampling to maximal-in-distributional-range mechanisms, at the price of truthfulness only in expectation.
--
--   **Formalization Note** Distributions are probability vectors on the finite $O$ and $W_{\mathcal D}$ is a supremum whose attainment is the stated hypothesis. Expectations are finite sums.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n} with n ≥ 2, nonnegative valuations on a nonempty finite outcome set O → Fin n with 2 ≤ n, real-valued functions O → ℝ with pointwise nonnegativity carried by the domain, Fintype O, Nonempty O, DecidableEq O; reason: relabeling and decidable finite membership change no instance
--   - encoding: a nonempty fixed collection 𝒟 of distributions over O, maxima assumed attained, a fixed tie-break rule among maximizing distributions → a nonempty Set of probability vectors (IsDistRange), W_𝒟 as sSup with the attainment predicate AttainsDistMax as hypothesis, and a universally quantified rule tbD with IsDistTieBreak; reason: O is finite, so distributions are probability vectors; the attainment hypothesis is the paper's
--   - generalization: every valuation profile (by default all nonnegative valuations) → every profile in arbitrary domains V i of nonnegative valuations, reports and deviations in V; reason: specializes to the paper's default domain
--   - generalization: ex-post IR for every outcome-payment pair in the support → v_i(o) − p_i(o; R_k) ≥ 0 for every seed (k, R_k) and every outcome o ∈ O; reason: covers the support; the proof sketch (PDF 20) shows the bound for every realized o
--   - reading: the theorem's conclusions (TIE, EPIR, the bound) → an additional conjunct: nonnegative payments for every seed and outcome; reason: §2 requires every mechanism's payments to lie in ℝ≥0; the proof sketch shows 0 ≤ p_i(o; T)
--   - generalization: 𝒟 is an α-approximate distributional range (α ≥ 1 by §2) → every real α > 0; reason: covers every α ≥ 1; for α < 1 the hypothesis forces W(N) = 0
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, Theorem 5, PDF p. 19 (printed p. 18); App. B.2 (attainment assumption, W_D, D_{R_k}, a_i, p_i, realized payment), PDF p. 19 (printed p. 18); proof sketch PDF p. 20 (printed p. 19)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model
import Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_MIDR

namespace MoneyBurningSurplus.Harmonic.Supplement

theorem theorem_5
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (Dset : Set (O → ℝ)) (hD : IsDistRange Dset)
    (tbD : Set (O → ℝ) → (O → ℝ)) (htbD : IsDistTieBreak tbD)
    (V : Fin n → Set (O → ℝ)) (hV : ∀ i, ∀ u ∈ V i, ∀ o, 0 ≤ u o)
    (hatt : AttainsDistMax Dset V) :
    (∀ v : Fin n → O → ℝ, AGT.IsValProfile V v → ∀ i : Fin n, ∀ v' ∈ V i,
      midrExpectedUtility tbD Dset (v i) i (Function.update v i v') ≤
        midrExpectedUtility tbD Dset (v i) i v) ∧
    (∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
      ∀ k ∈ Finset.Icc 1 n, ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∀ o : O, ∀ i : Fin n,
          0 ≤ v i o - midrPay tbD Dset T i v o) ∧
    (∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
      ∀ k ∈ Finset.Icc 1 n, ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∀ o : O, ∀ i : Fin n, 0 ≤ midrPay tbD Dset T i v o) ∧
    (∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
      distWelfare Dset v Finset.univ / (harmonic n : ℝ) ≤ midrSurplus tbD Dset v) ∧
    (∀ α : ℝ, 0 < α →
      (∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
        welfare v Finset.univ / α ≤ distWelfare Dset v Finset.univ) →
      ∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
        welfare v Finset.univ / (α * (harmonic n : ℝ)) ≤ midrSurplus tbD Dset v) := by sorry

end MoneyBurningSurplus.Harmonic.Supplement
