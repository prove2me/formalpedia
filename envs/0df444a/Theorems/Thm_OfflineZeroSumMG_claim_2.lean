-- Prove2me | Theorems.Thm_OfflineZeroSumMG_claim_2
-- name    : OfflineZeroSumMG.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:41.983411+00:00
-- url     : https://prove2.me/theorems/5777ea7b-eb06-4f48-95d5-cfebe8c4d748
-- title:
--   Claim 2 (corrected: $8\log(N/\delta)$ and $e\cdot\delta\le N$) — $\max\{N(s,a,b),8\log\frac N\delta\}\ge\frac12Nd_{\mathsf b}(s,a,b)$
-- statement:
--   Let the dataset be drawn as in (2.4) from $d_{\mathsf b}\in\Delta(\mathcal S\times\mathcal A\times\mathcal B)$ and a kernel $P$, with counts $N(s,a,b)$. For every $\delta\in(0,1)$ and every $N$ with $e\cdot\delta\le N$, with probability exceeding $1-\delta$,
--   $$\max\Big\{N(s,a,b),\ 8\log\frac N\delta\Big\}\ge\frac12N\,d_{\mathsf b}(s,a,b)\qquad\text{for all }(s,a,b)\in\mathcal S\times\mathcal A\times\mathcal B.$$
--
--   Every well-covered triple is thus sampled at least half as often as expected; this converts $1/N(s,a,b)$ into $1/(Nd_{\mathsf b}(s,a,b))$ in the proof of Lemma 5.
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: probability over the dataset drawn as in (2.4) → `dataProb`: the finite sum over datasets $D:\{1,\dots,N\}\to\mathcal S\times\mathcal A\times\mathcal B\times\mathcal S$ of $\prod_i d_{\mathsf b}(s_i,a_i,b_i)P(s'_i\mid s_i,a_i,b_i)$; reason: this is the law (2.4) on a finite sample space
--   - correction: $\max\{N(s,a,b),\log\frac N\delta\}$ → $\max\{N(s,a,b),8\log\frac N\delta\}$; reason: the printed claim is false (paper.md C4: $S=2$, $A=B=1$, $N=1000$, $\delta=10^{-6}$, $d_{\mathsf b}(1,1,1)=0.05$ give $\log(N/\delta)=20.7<25$ and $\mathbb P(\mathrm{Bin}(1000,0.05)<25)=2.4\cdot10^{-5}>\delta$); the proof's Chernoff base $1/(2e)$ should be $2/e$, and the factor $8$ restores the union bound
--   - correction: no condition relating $N$ and $\delta$ → $e\cdot\delta\le N$; reason: with only the factor $8$ the claim still fails at $N=1$: $S=2$, $A=B=1$, $d_{\mathsf b}=(1/2,1/2)$, $\delta=0.99$ give $8\log(1/\delta)\approx0.08<1/4$, and one triple always has count $0$, so the event has probability $0$; under $e\delta\le N$ the factor-8 Chernoff and union bound go through, and of its two users Lemma 5 assumes it, while Claim 3 holds trivially for $N\le4$ (the penalty forces $V^-_{\mathsf{pe}}\equiv0$) and $e\delta\le N$ is automatic for $N\ge3$
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), Claim 2, (C.40), p.31 (proof: Appendix C.6.1)

import Mathlib
import Definitions.Def_OfflineZeroSumMG_OfflineData

namespace OfflineZeroSumMG

/-- Claim 2 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.31), corrected (constant `8`, and
`e·δ ≤ N`): with probability exceeding `1 − δ`, `max{N(s, a, b), 8 log(N/δ)} ≥ (1/2) N d_b(s, a, b)`
holds for all `(s, a, b) ∈ S × A × B` (C.40).

**Formalization Note.** The printed claim has `log(N/δ)` in place of `8 log(N/δ)` and no
condition on `N/δ`; both versions are false without the correction (counterexamples in the
item's natural-language statement). The data law is (2.4). -/
theorem claim_2 {S A B : ℕ} (hS : 0 < S) (hA : 0 < A) (hB : 0 < B)
    (P : Kernel S A B) (hP : ∀ s a b, P s a b ∈ stdSimplex ℝ (Fin S))
    (db : Fin S → Fin A → Fin B → ℝ) (hdb : IsDist db)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (N : ℕ) (hN : Real.exp 1 * δ ≤ (N : ℝ)) :
    1 - δ < dataProb db P N (fun D => ∀ s a b,
      1 / 2 * (N : ℝ) * db s a b ≤ max (cnt D s a b : ℝ) (8 * Real.log ((N : ℝ) / δ))) := by sorry

end OfflineZeroSumMG
