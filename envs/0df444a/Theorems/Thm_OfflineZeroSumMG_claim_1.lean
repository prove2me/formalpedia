-- Prove2me | Theorems.Thm_OfflineZeroSumMG_claim_1
-- name    : OfflineZeroSumMG.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:43.794775+00:00
-- url     : https://prove2.me/theorems/da07e4d1-7cfa-4750-8827-66e68603e94a
-- title:
--   Claim 1 (corrected: $\delta\le1/e$) — Bernstein bound with plug-in variance for a fixed $V$
-- statement:
--   Let $p\in\Delta(\mathcal S)$ be a probability vector on $S\ge1$ states (the row $P_{s_0,a,b}$), let $\widehat p$ be the empirical distribution of $n\ge1$ independent draws from $p$ (the row $\widehat P_{s_0,a,b}$ given $N(s_0,a,b)=n$), let $\gamma\in(0,1)$, and let $V:\mathcal S\to[0,\frac1{1-\gamma}]$ be fixed (hence independent of $\widehat p$). There is a universal constant $C_0>0$ such that for every $\delta\in(0,1/e]$, with probability exceeding $1-\delta$,
--   $$\big|(\widehat p-p)V\big|\le C_0\sqrt{\frac1n\mathrm{Var}_{\widehat p}(V)\log\frac1\delta}+\frac{C_0\log\frac1\delta}{(1-\gamma)n}\qquad\text{(C.17)}$$
--   and
--   $$\mathrm{Var}_{\widehat p}(V)\le2\,\mathrm{Var}_p(V)+\frac{C_0\log\frac1\delta}{(1-\gamma)^2n}.\qquad\text{(C.18)}$$
--
--   This empirical Bernstein inequality is the concentration step of the leave-one-out argument behind Lemma 2.
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - correction: $\delta\in(0,1)$ → $\delta\in(0,1/e]$; reason: false for $\delta$ near $1$ (paper.md C3: $n=1$, $p$ uniform on two states, $V=(0,1/(1-\gamma))$ give $|(\widehat p-p)V|=1/(2(1-\gamma))$ and $\mathrm{Var}_{\widehat p}(V)=0$ almost surely, so (C.17) fails once $C_0\log(1/\delta)<1/2$); Lemma 2 applies the claim with $\delta/N$, where $\log(N/\delta)\ge1$
--   - reading: a statement about $\widehat P_{s_0,a,b}$, conditional on the counts $N(\cdot)$ (p.25), for $V$ "independent of $\widehat P_{s_0,a,b}$" → a statement about the empirical law of $n$ i.i.d. draws from $p=P_{s_0,a,b}$, for a fixed $V$; reason: given $N(s_0,a,b)=n$ the next states from $(s_0,a,b)$ are $n$ i.i.d. draws from $P_{s_0,a,b}$ (R4)
--   - reading: $O\big(\frac{1}{(1-\gamma)^2N(s_0,a,b)}\log\frac1\delta\big)$ in (C.18) → the same universal constant $C_0$ times $\frac{\log(1/\delta)}{(1-\gamma)^2n}$; reason: the hidden constant is universal (R3)
--   - generalization: the standing $1/2\le\gamma<1$ of Theorem 3 → $0<\gamma<1$; reason: the claim only uses $\gamma$ through the range of $V$; it specializes to $\gamma\ge1/2$
--   - encoding: probability over $\widehat P_{s_0,a,b}$ → `iidProb`: the finite sum over $X\in\mathcal S^n$ of $\prod_ip(X_i)$; reason: the law of $n$ i.i.d. draws on a finite set
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), Claim 1, (C.17)–(C.18), p.25 (proof: Appendix C.3.1)

import Mathlib
import Definitions.Def_OfflineZeroSumMG_OfflineData

namespace OfflineZeroSumMG

/-- Claim 1 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.25), corrected (`δ ≤ 1/e`): a
Bernstein bound with plug-in variance, and a bound on the plug-in variance, for a fixed
`V : S → [0, 1/(1−γ)]`. There is a universal `C₀ > 0` such that, if `P̂_{s₀,a,b}` is the empirical
law of `n = N(s₀, a, b) ≥ 1` independent draws from `P_{s₀,a,b}`, then with probability exceeding
`1 − δ`

`|(P̂_{s₀,a,b} − P_{s₀,a,b})V| ≤ C₀ √((1/n) Var_{P̂}(V) log(1/δ)) + C₀ log(1/δ)/((1−γ) n)` (C.17)

and `Var_{P̂}(V) ≤ 2 Var_P(V) + C₀ log(1/δ)/((1−γ)² n)` (C.18).

**Formalization Note.** The paper's statement is conditional on the counts `N(s, a, b)`
(p.25, "all the probabilistic arguments below are conditional on {N(s,a,b)}"); given
`N(s₀, a, b) = n`, the next states from `(s₀, a, b)` are `n` i.i.d. draws from `p = P_{s₀,a,b}`,
which is the model here (`iidProb`, `empirical`). `V` is fixed, so it is independent of `P̂`.
The `O(·)` in (C.18) uses the same universal constant `C₀`. -/
theorem claim_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (S : ℕ), 0 < S →
    ∀ p : Fin S → ℝ, p ∈ stdSimplex ℝ (Fin S) →
    ∀ n : ℕ, 1 ≤ n →
    ∀ γ : ℝ, 0 < γ → γ < 1 →
    ∀ V : Fin S → ℝ, (∀ s, 0 ≤ V s ∧ V s ≤ 1 / (1 - γ)) →
    ∀ δ : ℝ, 0 < δ → δ ≤ Real.exp (-1) →
      1 - δ < iidProb p n (fun X =>
        |∑ s, (empirical X s - p s) * V s| ≤
            C₀ * Real.sqrt (1 / (n : ℝ) * varP (empirical X) V * Real.log (1 / δ)) +
            C₀ * Real.log (1 / δ) / ((1 - γ) * (n : ℝ)) ∧
        varP (empirical X) V ≤
            2 * varP p V + C₀ * Real.log (1 / δ) / ((1 - γ) ^ 2 * (n : ℝ))) := by sorry

end OfflineZeroSumMG
