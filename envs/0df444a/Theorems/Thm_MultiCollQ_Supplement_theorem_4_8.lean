-- Prove2me | Theorems.Thm_MultiCollQ_Supplement_theorem_4_8
-- name    : MultiCollQ.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:02:22.103987+00:00
-- url     : https://prove2.me/theorems/c352b4f9-0a19-4a0d-a8c6-bf4070f7836f
-- title:
--   Theorem 4.8 — upper bound $O_{k,r}(\tau_{r,\ell}(N,n_*))$ with forward permutation access, success with certainty
-- statement:
--   Fix $k\ge r\ge2$ and a public bucket partition $Q_1,\dots,Q_h$ of $[N]$ of type $(1^{n_1},\dots,k^{n_k})$, and let $n_*=\sum_{i=r}^kn_i\ge1$. For every integer $1\le\ell\le n_*$ there is a quantum algorithm that, for every permutation $\pi\in S_N$, finds $r$ distinct preimages in each of $\ell$ distinct buckets using
--
--   $$
--   O_{k,r}\Bigl(\frac{\sqrt N\,\ell^{1/(2-2^{1-r})}}{n_*^{1/(2^{r+1}-2)}}\Bigr) \tag{4.31}
--   $$
--
--   forward swap queries to $P_\pi$. The algorithm succeeds with certainty and does not require queries to $\pi^{-1}$.
--
--   This matches the scale of Theorem 4.6 for every $1\le\ell\le n_*$, so the database tail is tight in the public-bucket model.
--
--   **Formalization Note** $O_{k,r}$ is stated as: there is $C>0$ depending only on $k,r$ such that for every partition and every $\ell$ there are a forward permutation-query algorithm (finite workspace, forward swap queries only, independent of $\pi$), a query count $T\le C\,\tau_{r,\ell}(N,n_*)$ and an output map, such that for every $\pi$ the measured output satisfies the bucket multi-collision relation with probability exactly $1$.
--
--   Differences from the source:
--   - reading: O_{k,r}(τ_{r,ℓ}(N, n_*)) forward swap queries → ∃ C > 0 depending on k, r only, before the partition and ℓ; T ≤ C·τ_{r,ℓ}(N, n_*); reason: the subscripts say C depends on k, r only
--   - encoding: public buckets of exact type λ = (1^{n_1}, …, k^{n_k}), N = Σ i n_i, h = Σ n_i → n : ℕ → ℕ read at 1..k and HasBucketType b k n; reason: the bucket condition forces N = Σ i n_i and h = Σ n_i; same instances
--   - encoding: a quantum algorithm with intermediate measurements whose query bound holds for every sequence of measured outcomes, succeeding with certainty → a MultiCollQ.FwdAlg (unitaries, forward swap queries realStep only) making exactly T queries, whose computational-basis measurement plus output map satisfies bucketCollRel with probability 1 for every π; reason: deferred measurement; branches needing fewer queries are padded (P_π² = I), so a fixed T bounded by the per-branch bound exists
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), Theorem 4.8, p.44, eq. (4.31)

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_MultiCollQ_Aconst
import Definitions.Def_MultiCollQ_FwdAlg
import Definitions.Def_MultiCollQ_Supplement_tauScale
import Definitions.Def_MultiCollQ_Supplement_bucketCollRel

namespace MultiCollQ.Supplement

open CompPermOracle

/-- Theorem 4.8 (Upper bound for arbitrary public bucket types) (Peng, Hou, Dong, *Quantum
multi-collision lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), p.44). Fix
`k ≥ r ≥ 2` and a public bucket partition `Q_1, …, Q_h` of `[N]` of type `(1^{n_1}, …, k^{n_k})`,
with `n_* = Σ_{i=r}^k n_i ≥ 1`. For every integer `1 ≤ ℓ ≤ n_*` there is a quantum algorithm that,
for every permutation `π ∈ S_N`, finds `r` distinct preimages in each of `ℓ` distinct buckets using
`O_{k,r}(√N ℓ^{1/(2−2^{1−r})} / n_*^{1/(2^{r+1}−2)})` (4.31) forward swap queries to `P_π`. The
algorithm succeeds with certainty and does not require queries to `π^{−1}`.

**Formalization Note.** `O_{k,r}` is pinned as `∃ C > 0` depending only on `k, r`, chosen before
`N`, the partition `b : Fin N → Fin h` (`HasBucketType b k n`) and `ℓ`. The algorithm is a
`MultiCollQ.FwdAlg` (forward swap queries `P_π` only; no inverse access) with a finite workspace
`Fin wb`; it may depend on the public partition and on `ℓ` but not on `π`. It makes `T` queries
with `T ≤ C·τ_{r,ℓ}(N, n_*)` (`tauScale`, (4.25)), and for every `π` the computational-basis
measurement of `A.realState π T` followed by the output map `out` gives, with probability exactly
`1`, `ℓ` groups of `r` distinct inputs whose images lie in one bucket per group, with distinct
buckets for distinct groups (`bucketCollRel`). -/
theorem theorem_4_8 (k r : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N h : ℕ} (b : Fin N → Fin h) (n : ℕ → ℕ), HasBucketType b k n →
      1 ≤ nStar k r n → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ nStar k r n →
      ∃ (wb T : ℕ) (A : FwdAlg N (Fin wb)) (out : FAcc N (Fin wb) → (Fin ℓ → Fin r → Fin N)),
        (T : ℝ) ≤ C * tauScale r ℓ N (nStar k r n) ∧
        ∀ π : Equiv.Perm (Fin N), realSuccessProb A π T out (bucketCollRel r ℓ b π) = 1 := by sorry

end MultiCollQ.Supplement
