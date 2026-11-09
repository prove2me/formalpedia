-- Prove2me | Theorems.Thm_KTaxi_Competitive_lemma_4_3
-- name    : KTaxi.Competitive.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:56.994663+00:00
-- url     : https://prove2.me/theorems/25151b21-86d2-4b2b-adf0-6242e03e8a58
-- title:
--   Lemma 4.3 — expected movement cost $\mathbb E[\mathrm{ALG}_t]=3^{k-1}/Z_k$
-- statement:
--   Fix a round with request $(r,s)$ and condition on the current ordered list $x$; let $d_i=d(x_i,r)$ and $Z_k=\sum_{i=1}^k w_i/d_i$.
--
--   1. If $d_i>0$ for all $1\le i\le k$, the expected movement cost of Algorithm 1 in this round is
--   $$
--   \mathbb E[\mathrm{ALG}_t]=\frac{3^{k-1}}{Z_k}.
--   $$
--   2. Otherwise, if $d_i=0$ for some $i$, then $\mathrm{ALG}_t=0$: every list update of positive probability puts a taxi located at $r$ in the first position.
--
--   This is the movement cost that the potential decrease must pay for in Property 4.1.
--
--   **Formalization Note** The expectation is the finite sum over list updates $\pi$ weighted by `scanLaw x r`, and $\mathrm{ALG}_t=d(x_{\pi(1)},r)$.
--
--   Differences from the source:
--   - encoding: 1-based ranks i = 1, …, k → 0-based slots j : Fin k (rank j + 1); levels m : ℕ count leading slots; reason: Lean convention; same instances
--   - encoding: if d_i = 0 for some i, ALG_t = 0 → ALG_t = 0 for every list update of positive probability; reason: ALG_t = 0 holds almost surely: an exponential clock equals 0 with probability 0
--   - generalization: k ≥ 2 (standing assumption, PDF p. 4) → k ≥ 1, including the one-taxi case; reason: the statement also holds for one taxi and specializes to every k ≥ 2; at k = 1 the scan is the identity, the matching has one edge, and any lower-level sum is empty
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Lemma 4.3, PDF p. 7 (printed p. 6)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Analysis

namespace KTaxi.Competitive

/-- **Lemma 4.3** (expected movement cost; PDF p. 7). Fix the ordered list `x` and the pickup
`r`, with `d_i = d(x_i, r)`. If `d_i > 0` for every slot, the expected movement cost of one round
of Algorithm 1 is `E[ALG_t] = 3^{k-1} / Z_k`. Otherwise, if `d_i = 0` for some slot, the
movement cost is `0` for every list update of positive probability. -/
theorem lemma_4_3 {V : Type*} [MetricSpace V] {k : ℕ} [NeZero k] (x : Fin k → V) (r : V) :
    ((∀ i, 0 < dist (x i) r) →
      ∑ π : Equiv.Perm (Fin k), (scanLaw x r π).toReal * dist (x (π 0)) r =
        3 ^ (k - 1) / normZ x r k) ∧
    ((∃ i, dist (x i) r = 0) →
      ∀ π : Equiv.Perm (Fin k), scanLaw x r π ≠ 0 → dist (x (π 0)) r = 0) := by sorry

end KTaxi.Competitive
