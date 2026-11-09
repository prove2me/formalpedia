-- Prove2me | Theorems.Thm_KTaxi_Competitive_expected_level_change
-- name    : KTaxi.Competitive.expected_level_change
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:29:28.562354+00:00
-- url     : https://prove2.me/theorems/6bb74542-b37a-46e9-a90e-49ab7b38d8eb
-- title:
--   §4.2 — expected potential change $\mathbb E[\Delta\Phi]=\sum_m\frac{\alpha_m}{Z_m}\sum_{i\le m}\frac{w_i}{d_i}\Delta_{m,i}$
-- statement:
--   Let $x$ be an online ordered list and $r$ the pickup, with $d_i=d(x_i,r)>0$ for all $1\le i\le k$, and let $Y$ be an adversary configuration and $\alpha_1,\dots,\alpha_k$ any coefficients. During one round of Algorithm 1 (list update and movement to $r$) the expected change of the potential $\Phi(x,Y)=\sum_m\alpha_mD(X_m,Y)$ is
--   $$
--   \mathbb E[\Delta\Phi]=\sum_{m=1}^k\frac{\alpha_m}{Z_m}\sum_{i=1}^m\frac{w_i}{d_i}\,\Delta_{m,i}=\sum_{m=1}^k\frac{\alpha_m}{Z_m}\Delta_m ,
--   $$
--   where $\Delta_{m,i}=D(X_m-x_i+r,Y)-D(X_m,Y)$ and $Z_m=\sum_{i\le m}w_i/d_i$. The reason is that the local winner of the level-$m$ prefix is $x_i$ with probability $w_i/(d_iZ_m)$, in which case $X_m$ becomes $X_m-x_i+r$.
--
--   Differences from the source:
--   - encoding: 1-based ranks i = 1, …, k → 0-based slots j : Fin k (rank j + 1); levels m : ℕ count leading slots; reason: Lean convention; same instances
--   - generalization: Y an adversary configuration containing r, and the coefficients α_1 > ⋯ > α_k > 0 → any adversary configuration Y and any real coefficients α; reason: the identity uses neither; the paper's case is an instance
--   - generalization: k ≥ 2 (standing assumption, PDF p. 4) → k ≥ 1, including the one-taxi case; reason: the statement also holds for one taxi and specializes to every k ≥ 2; at k = 1 the scan is the identity, the matching has one edge, and any lower-level sum is empty
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §4.2, display for E[ΔΦ], PDF p. 8 (printed p. 7)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Analysis

namespace KTaxi.Competitive

/-- **§4.2, expected change of the potential** (PDF p. 8). If `d_i = d(x_i, r) > 0` for every
slot, then for every adversary configuration `Y` and all coefficients `α`, the expected change of
the potential during one round of Algorithm 1 (list update and movement to `r`) is
`E[ΔΦ] = ∑_{m=1}^k (α_m / Z_m) ∑_{i ≤ m} (w_i / d_i) Δ_{m,i} = ∑_{m=1}^k (α_m / Z_m) Δ_m`. -/
theorem expected_level_change {V : Type*} [MetricSpace V] {k : ℕ} [NeZero k] (α : ℕ → ℝ)
    (x Y : Fin k → V) (r : V) (hpos : ∀ i, 0 < dist (x i) r) :
    ∑ π : Equiv.Perm (Fin k), (scanLaw x r π).toReal *
        (potential α (afterRound x π r) Y - potential α x Y) =
      ∑ m ∈ Finset.Icc 1 k, α m / normZ x r m * levelDelta x Y r m := by sorry

end KTaxi.Competitive
