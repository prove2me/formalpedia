-- Prove2me | Theorems.Thm_MultiCollQ_corollary_3_5
-- name    : MultiCollQ.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:44.534219+00:00
-- url     : https://prove2.me/theorems/7c3a5606-e71f-47f4-8ea2-fd5f21ced8f6
-- title:
--   Corollary 3.5 — multi-target bound $a_{r,\ell}(T)^2\le\min\{1,m_r(T)/\ell\}\le\min\{1,A_rT^{\alpha_r}/(\ell(N-T)^{\beta_r})\}$
-- statement:
--   Let the public buckets have sizes at most $k$ and $2\le r\le k$. For every forward compressed-query algorithm, every integer $1\le T<N$ and every integer $\ell\ge1$,
--
--   $$
--   a_{r,\ell}(T)^2\le\min\Bigl\{1,\frac{m_r(T)}{\ell}\Bigr\}\le\min\Bigl\{1,\frac{A_rT^{\alpha_r}}{\ell\,(N-T)^{\beta_r}}\Bigr\}.
--   $$
--
--   Combined with Theorem 2.7 this gives the query lower bound of Corollary 3.6.
--
--   **Formalization Note** The algorithm is any `FwdAlg`; real powers.
--
--   Differences from the source:
--   - generalization: $1\le\ell\le n$ → every integer $\ell\ge1$; reason: the bound holds for every $\ell\ge1$ and specializes to the source's range
--   - encoding: the algorithm models (start state and unitaries independent of the oracle, measurement of the output register) → `FwdAlg` and its compressed state; reason: same class of algorithms
--   - encoding: $[N]$ and the buckets $Q_1,\dots,Q_h$ with $d_b\le k$ (§3, p.18) → `Fin N` (0-based) and a bucket map `b : Fin N → Fin h` with `BucketsBounded b k` (sizes in $[1,k]$); reason: Lean convention; blocks of a partition are nonempty; same instances
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Corollary 3.5, (3.15), p.26

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_MultiCollQ_Aconst
import Definitions.Def_MultiCollQ_FwdAlg

namespace MultiCollQ

open CompPermOracle

/-- Corollary 3.5 (Multi-target bound from the first moment) (Peng, Hou, Dong, manuscript
(Oct. 2026), p.26). For buckets of sizes at most `k`, `2 ≤ r ≤ k`, every forward compressed-query
algorithm, every integer `1 ≤ T < N` and every integer `ℓ ≥ 1`:
`a_{r,ℓ}(T)² ≤ min{1, m_r(T)/ℓ} ≤ min{1, A_r T^{α_r} / (ℓ (N − T)^{β_r})}` (3.15).

**Formalization Note.** The paper's range `1 ≤ ℓ ≤ n` (`n` the number of buckets) is widened to
every `ℓ ≥ 1`. Real powers. -/
theorem corollary_3_5 {N h k r T ℓ : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk]
    (b : Fin N → Fin h) (hb : BucketsBounded b k) (A : FwdAlg N Wk) (hr : 2 ≤ r) (hrk : r ≤ k)
    (hT : 1 ≤ T) (hTN : T < N) (hℓ : 1 ≤ ℓ) :
    dbAmp b r ℓ (A.compressedState T) ^ 2 ≤ min 1 (firstMoment b r (A.compressedState T) / ℓ) ∧
    min 1 (firstMoment b r (A.compressedState T) / ℓ) ≤
      min 1 (Aconst k r * (T : ℝ) ^ alphaExp r / ((ℓ : ℝ) * ((N : ℝ) - T) ^ betaExp r)) := by sorry

end MultiCollQ
