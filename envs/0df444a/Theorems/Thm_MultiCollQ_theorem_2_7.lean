-- Prove2me | Theorems.Thm_MultiCollQ_theorem_2_7
-- name    : MultiCollQ.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:29.375257+00:00
-- url     : https://prove2.me/theorems/a7e9367c-e24c-483a-972a-bfdf73e9c0ad
-- title:
--   Theorem 2.7 — conversion to real success probability: $\sqrt p\le a_{r,\ell}(2t+r\ell)+r\ell\sqrt{2/(N-2t-r\ell)}+\delta_N(2t+2r\ell)$
-- statement:
--   Fix an exact type $\lambda=(1^{n_1},\dots,k^{n_k})$ with $N=\sum_i i\,n_i\ge3$ and $h=\sum_i n_i$, an alphabet size $q\ge h$, public buckets partitioning $[N]$ with size multiset $\lambda$, and integers $2\le r\le k$, $1\le\ell\le\sum_{i=r}^{k}n_i$. Suppose an algorithm makes $t$ phase queries $O_f|x,c,z\rangle=\omega_q^{cf(x)}|x,c,z\rangle$ and finds $\ell$ $r$-collisions in distinct equality classes with probability $p$, averaged over the uniform distribution on $F_{\lambda,q}$. If $6t+6r\ell-1\le N$, then there is a forward permutation-query algorithm making $2t+r\ell$ compressed queries such that
--
--   $$
--   \sqrt p\le a_{r,\ell}(2t+r\ell)+r\ell\sqrt{\frac{2}{N-2t-r\ell}}+\delta_N(2t+2r\ell),
--   $$
--
--   where $a_{r,\ell}(s)=\|P_{r,\ell}\zeta_s\|$ is its database amplitude for the event $C_r\ge\ell$ ($\ell$ buckets holding at least $r$ recorded images).
--
--   This reduces the function-query lower bound to a bound on $a_{r,\ell}$ valid for every forward compressed-query algorithm.
--
--   **Formalization Note** The constructed algorithm is an `FwdAlg` with auxiliary register `Fin w` and may depend on the buckets and all other data.
--
--   Differences from the source:
--   - reading: an algorithm making at most $2t+r\ell$ compressed queries, with $a_{r,\ell}(2t+r\ell)$ its amplitude → an algorithm making exactly $2t+r\ell$ queries; reason: the amplitude is evaluated after $2t+r\ell$ queries, and the construction reads all $r\ell$ reported inputs; the exact count implies the printed one
--   - encoding: $6t+6r\ell-1\le N$ → `6 * t + 6 * r * ℓ ≤ N + 1`; reason: same condition in natural numbers
--   - encoding: the type $\lambda$ with $N=\sum i n_i$, $h=\sum n_i$ and buckets of size multiset $\lambda$ → `n : ℕ → ℕ` and `b : Fin N → Fin h` with `HasBucketType b k n`; reason: the bucket condition implies $N=\sum i n_i$ and $h=\sum n_i$
--   - encoding: the algorithm models (start state and unitaries independent of the oracle, measurement of the output register) → `QAlgorithms.QueryAlg` with the phase oracle and an output map to $\ell$ groups of $r$ inputs; `FwdAlg` for the constructed algorithm; reason: same classes of algorithms
--   - encoding: $[N]$, $[h]$, $\mathbb Z_q$ → `Fin N`, `Fin h` (0-based), `ZMod q` with `[NeZero q]`; reason: Lean convention; same instances ($q\ge1$ on every range used)
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Theorem 2.7, p.15 (setting of §2.4, pp.13–14)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_HasExactType
import Definitions.Def_MultiCollQ_collisionRel
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_MultiCollQ_deltaN
import Definitions.Def_MultiCollQ_FwdAlg

namespace MultiCollQ

open QAlgorithms CompPermOracle

/-- Theorem 2.7 (Conversion to real success probability) (Peng, Hou, Dong, manuscript (Oct. 2026),
p.15), in the setting of §2.4 (p.13): an exact type `λ = (1^{n_1}, …, k^{n_k})` with
`N = Σ i n_i ≥ 3`, `h = Σ n_i`, alphabet size `q ≥ h`, public buckets `b` with size multiset `λ`,
`2 ≤ r ≤ k` and `1 ≤ ℓ ≤ Σ_{i=r}^k n_i`. Suppose an algorithm makes `t` function phase queries and
finds `ℓ` `r`-collisions in distinct equality classes with probability `p`, averaged over the uniform
distribution on `F_{λ,q}`. If `6t + 6rℓ − 1 ≤ N`, then there is an algorithm making `2t + rℓ`
forward compressed permutation queries such that
`√p ≤ a_{r,ℓ}(2t + rℓ) + rℓ √(2/(N − 2t − rℓ)) + δ_N(2t + 2rℓ)` (2.9).

**Formalization Note.** The function-query algorithm is `QAlgorithms.QueryAlg` with the phase oracle
(2.1), workspace `Fin wb` for any `wb`, and output map `out` to `ℓ` groups of `r` inputs. The
constructed algorithm is a forward-only `FwdAlg` with auxiliary register `Fin w`; it may depend on
the buckets and all data. Its query count is stated as exactly `2t + rℓ` (the paper's "at most";
the construction reads all `rℓ` reported inputs). `a_{r,ℓ}` is `dbAmp b r ℓ` of its compressed
state. `6t + 6rℓ − 1 ≤ N` is written `6t + 6rℓ ≤ N + 1`. -/
theorem theorem_2_7 {N h q k : ℕ} [NeZero q] (n : ℕ → ℕ) (b : Fin N → Fin h)
    (hb : HasBucketType b k n) (hN : 3 ≤ N) (hq : h ≤ q) {r ℓ : ℕ} (hr : 2 ≤ r) (hrk : r ≤ k)
    (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ ∑ i ∈ Finset.Icc r k, n i) {t wb : ℕ}
    (A : QueryAlg (Fin N) (ZMod q) (Fin wb) t)
    (out : (Fin N × ZMod q) × Fin wb → (Fin ℓ → Fin r → Fin N))
    (ht : 6 * t + 6 * r * ℓ ≤ N + 1) :
    ∃ (w : ℕ) (B : FwdAlg N (Fin w)),
      Real.sqrt (avgSuccess (exactTypeSet N q k n) A out (collisionRel r ℓ)) ≤
        dbAmp b r ℓ (B.compressedState (2 * t + r * ℓ)) +
          ((r * ℓ : ℕ) : ℝ) * Real.sqrt (2 / ((N : ℝ) - (2 * t + r * ℓ : ℕ))) +
          deltaN N (2 * t + 2 * r * ℓ) := by sorry

end MultiCollQ
