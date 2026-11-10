-- Prove2me | Theorems.Thm_MultiCollQ_lemma_3_3
-- name    : MultiCollQ.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:22.935764+00:00
-- url     : https://prove2.me/theorems/8e8367c2-6a62-46a3-a862-16ffc488770b
-- title:
--   Lemma 3.3 — weighted increments $|m_j(s+1)-m_j(s)|,\ a_{j,1}(s+1)-a_{j,1}(s)\le c_j\sqrt{m_{j-1}(s)/(N-s)}$
-- statement:
--   Let the public buckets have sizes at most $k$, and let $\zeta_s$ be the joint state after $s$ queries of any forward compressed-query algorithm. For every $2\le j\le k$ and $s<N$,
--
--   $$
--   |m_j(s+1)-m_j(s)|\le c_j\sqrt{\frac{m_{j-1}(s)}{N-s}},\qquad a_{j,1}(s+1)-a_{j,1}(s)\le c_j\sqrt{\frac{m_{j-1}(s)}{N-s}},
--   $$
--
--   where $c_j=\sqrt{8(k-j+1)}$, $m_j(s)=\langle\zeta_s,\widehat C_j\zeta_s\rangle$ and $a_{j,1}(s)=\|P_{j,1}\zeta_s\|$.
--
--   These are the first-moment and single-target recurrences that Theorem 3.4 sums over $s$.
--
--   **Formalization Note** The algorithm is any `FwdAlg`.
--
--   Differences from the source:
--   - encoding: the algorithm models (start state and unitaries independent of the oracle, measurement of the output register) → `FwdAlg` and its compressed state, $U_0$ absorbed into the initial state; reason: same class of algorithms
--   - encoding: $[N]$ and the buckets $Q_1,\dots,Q_h$ with $d_b\le k$ (§3, p.18) → `Fin N` (0-based) and a bucket map `b : Fin N → Fin h` with `BucketsBounded b k` (sizes in $[1,k]$); reason: Lean convention; blocks of a partition are nonempty; same instances
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Lemma 3.3, (3.10)–(3.11), p.23

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

/-- Lemma 3.3 (Weighted increments for first moments and single-target norms) (Peng, Hou, Dong,
manuscript (Oct. 2026), p.23). For buckets of sizes at most `k`, every forward compressed-query
algorithm, every `2 ≤ j ≤ k` and `s < N`:
`|m_j(s + 1) − m_j(s)| ≤ c_j √(m_{j−1}(s)/(N − s))` (3.10) and
`a_{j,1}(s + 1) − a_{j,1}(s) ≤ c_j √(m_{j−1}(s)/(N − s))` (3.11),
with `c_j = √(8(k − j + 1))`, `m_j(s) = ⟨ζ_s, Ĉ_j ζ_s⟩`, `a_{j,1}(s) = ‖P_{j,1} ζ_s‖`.

**Formalization Note.** `ζ_s` is `A.compressedState s` for an arbitrary `FwdAlg` (any finite
auxiliary register, any unit initial state). -/
theorem lemma_3_3 {N h k j s : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk] (b : Fin N → Fin h)
    (hb : BucketsBounded b k) (A : FwdAlg N Wk) (hj : 2 ≤ j) (hjk : j ≤ k) (hs : s < N) :
    |firstMoment b j (A.compressedState (s + 1)) - firstMoment b j (A.compressedState s)| ≤
        cConst k j * Real.sqrt (firstMoment b (j - 1) (A.compressedState s) / ((N : ℝ) - s)) ∧
    dbAmp b j 1 (A.compressedState (s + 1)) - dbAmp b j 1 (A.compressedState s) ≤
        cConst k j * Real.sqrt (firstMoment b (j - 1) (A.compressedState s) / ((N : ℝ) - s)) := by sorry

end MultiCollQ
