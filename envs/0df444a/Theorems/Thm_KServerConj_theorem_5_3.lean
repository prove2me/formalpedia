-- Prove2me | Theorems.Thm_KServerConj_theorem_5_3
-- name    : KServerConj.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:33.441902+00:00
-- url     : https://prove2.me/theorems/dad5abde-f509-47e1-b74a-c46363d576a2
-- title:
--   Theorem 5.3 — telescoped bound: $\sum_t\mathrm{ExtCost}_t\le(k+1)w_T(X_T)+\mathrm{cl}(C_0)-\mathrm{cl}(X_T)$ and $\mathrm{WFA}\le k\,w_T(X_T)+\mathrm{cl}(C_0)-\mathrm{cl}(X_T)$
-- statement:
--   Let $M$ be a finite pseudometric space, $k\ge2$, $C_0$ a configuration of $k$ points and $r_1,\dots,r_T$ requests. Let $X_T$ be a configuration of $k$ points minimizing $w_T$. Then
--
--   $$\sum_{t=1}^T\mathrm{ExtCost}_t\le(k+1)\,w_T(X_T)+\mathrm{cl}(C_0)-\mathrm{cl}(X_T),\tag{26}$$
--
--   and for every WFA trajectory
--
--   $$\mathrm{WFA}_{C_0}(r_1,\dots,r_T)\le k\,w_T(X_T)+\mathrm{cl}(C_0)-\mathrm{cl}(X_T).\tag{27}$$
--
--   Since $\mathrm{cl}(X_T)\ge0$ and $w_T(X_T)=\mathrm{OPT}_{C_0}(r_1,\dots,r_T)$, (27) gives Theorem 1.3 on finite spaces.
--
--   Differences from the source:
--   - generalization: a metric space (M, d) → a pseudometric space (`PseudoMetricSpace M`); reason: the paper, p.1: "our proof works also when d is a pseudometric"; every metric space is a pseudometric space
--   - generalization: WFA_{C₀}(r₁, …, r_T), the cost of the (lazy) WFA → the cost of every WFA trajectory (IsWFATraj); reason: p.2: "our result extends to any other tie-breaking rule"; the lazy trajectory is one of them
--   - encoding: X_T a configuration minimizing w_T → X_T with card k and w_T(X_T) ≤ w_T(X) for every X with card k; reason: configurations are k-element sets
--   - encoding: k servers (k ≥ 2, standing assumption of §2–5) and a configuration C₀ → hypotheses 2 ≤ k and C₀.card = k; reason: the same assumptions
--   - encoding: a finite request sequence r₁, …, r_T → r : ℕ → M, with requests r 1, …, r T; reason: values of r outside 1, …, T enter no quantity of the statement
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), Theorem 5.3, p.13 (pdf p.14)

import Mathlib
import Definitions.Def_KServerConj_cl
import Definitions.Def_KServerConj_IsWFATraj
import Definitions.Def_KServerConj_extCost

namespace KServerConj

/-- **Theorem 5.3.** Coester, Koutsoupias, Zbysiński, *The k-server conjecture is true*,
arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), printed p.13 (PDF p.14): "Let X_T be a
configuration minimizing w_T. Then
∑_{t=1}^T ExtCost_t ≤ (k + 1)w_T(X_T) + cl(C₀) − cl(X_T), (26)
WFA_{C₀}(r₁, …, r_T) ≤ k w_T(X_T) + cl(C₀) − cl(X_T). (27)"

**Formalization Note.** `M` finite (printed p.1) and `k ≥ 2` (standing assumption, printed p.5).
`X_T` is any configuration of `k` points minimizing `w_T` over configurations, and (27) is asserted
for every WFA trajectory. -/
theorem theorem_5_3 {M : Type*} [PseudoMetricSpace M] [Fintype M] (k : ℕ) (hk : 2 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) (XT : Finset M) (hXT : XT.card = k)
    (hmin : ∀ X : Finset M, X.card = k → workFn k C₀ r T XT ≤ workFn k C₀ r T X) :
    (∑ t ∈ Finset.Icc 1 T, extCost k C₀ r t ≤
        ((k : ℝ) + 1) * workFn k C₀ r T XT + cl C₀ - cl XT) ∧
    ∀ C : ℕ → Finset M, IsWFATraj k C₀ r T C →
      wfaCost C T ≤ (k : ℝ) * workFn k C₀ r T XT + cl C₀ - cl XT := by sorry

end KServerConj
