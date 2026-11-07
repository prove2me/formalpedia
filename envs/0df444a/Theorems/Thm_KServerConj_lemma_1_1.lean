-- Prove2me | Theorems.Thm_KServerConj_lemma_1_1
-- name    : KServerConj.lemma_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:13.093789+00:00
-- url     : https://prove2.me/theorems/c8bd4cf0-1e37-4e19-a68d-4a260e1fc336
-- title:
--   Lemma 1.1 — extended-cost accounting: $\mathrm{WFA}+w_T(C_T)\le\sum_t\mathrm{ExtCost}_t$
-- statement:
--   Let $M$ be a finite pseudometric space, $k\ge1$, $C_0$ a configuration of $k$ points and $r_1,\dots,r_T$ requests. For every WFA trajectory $C_0,C_1,\dots,C_T$,
--
--   $$\mathrm{WFA}_{C_0}(r_1,\dots,r_T)+w_T(C_T)\le\sum_{t=1}^T\mathrm{ExtCost}_t,\qquad \mathrm{ExtCost}_t=\max_X\big(w_t(X)-w_{t-1}(X)\big).$$
--
--   This is the extended-cost method of Chrobak and Larmore: the cost of the algorithm is controlled by the total increase of the work function at the worst configurations, so it suffices to bound $\sum_t\mathrm{ExtCost}_t$.
--
--   Differences from the source:
--   - generalization: a metric space (M, d) → a pseudometric space (`PseudoMetricSpace M`); reason: the paper, p.1: "our proof works also when d is a pseudometric"; every metric space is a pseudometric space
--   - generalization: any WFA trajectory, the WFA being defined with a lazy tie-break → every trajectory of minimizers over all configurations containing r_t (IsWFATraj); reason: p.2: "our result extends to any other tie-breaking rule"; the lazy trajectory is one of them
--   - encoding: k servers and a configuration C₀ → hypotheses 1 ≤ k and C₀.card = k; reason: configurations are k-element sets
--   - encoding: a finite request sequence r₁, …, r_T → r : ℕ → M, with requests r 1, …, r T; reason: values of r outside 1, …, T enter no quantity of the statement
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), Lemma 1.1, p.2 (pdf p.3); proof in Appendix A, p.14 (pdf p.15)

import Mathlib
import Definitions.Def_KServerConj_IsWFATraj
import Definitions.Def_KServerConj_extCost

namespace KServerConj

/-- **Lemma 1.1 (Extended-cost accounting [CL92]).** Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), printed p.2
(PDF p.3): "Let C₀, C₁, …, C_T be any WFA trajectory, and let ExtCost_t = max_X(w_t(X) − w_{t−1}(X)).
Then WFA_{C₀}(r₁, …, r_T) + w_T(C_T) ≤ ∑_{t=1}^T ExtCost_t. (3)"

**Formalization Note.** `M` is finite (the paper's standing assumption, printed p.1), so the maximum
defining `ExtCost_t` exists. "Any WFA trajectory" is every `C` with `IsWFATraj`, whatever the
tie-break. -/
theorem lemma_1_1 {M : Type*} [PseudoMetricSpace M] [Fintype M] (k : ℕ) (hk : 1 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) (C : ℕ → Finset M)
    (hC : IsWFATraj k C₀ r T C) :
    wfaCost C T + workFn k C₀ r T (C T) ≤ ∑ t ∈ Finset.Icc 1 T, extCost k C₀ r t := by sorry

end KServerConj
