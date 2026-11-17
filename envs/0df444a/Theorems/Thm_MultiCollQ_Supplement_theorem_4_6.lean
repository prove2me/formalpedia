-- Prove2me | Theorems.Thm_MultiCollQ_Supplement_theorem_4_6
-- name    : MultiCollQ.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:01:44.162208+00:00
-- url     : https://prove2.me/theorems/b36f017c-996b-48bd-9766-6e19161f5594
-- title:
--   Theorem 4.6 — exponential database tail $a^*_{r,\ell}(T)\le\theta^\ell$ for all target counts
-- statement:
--   Fix $k\ge r\ge2$ and $\theta\in(0,1)$. There is a constant $c_{k,r,\theta}>0$ such that, for every domain size $N$, every public bucket partition of exact type $(1^{n_1},\dots,k^{n_k})$ with $n_*=\sum_{i=r}^kn_i\ge1$, every forward compressed-query algorithm and every integer $1\le\ell\le n_*$,
--
--   $$
--   a^*_{r,\ell}(T)\le\theta^{\ell}\quad\text{whenever}\quad 0\le T\le c_{k,r,\theta}\,\tau_{r,\ell}(N,n_*), \tag{4.26}
--   $$
--
--   where $\tau_{r,\ell}(N,n_*)=\sqrt N\,\ell^{1/(2-2^{1-r})}/n_*^{1/(2^{r+1}-2)}$ and the query count $T$ is an integer.
--
--   Unlike Theorem 3.8 this holds for every type and every $1\le\ell\le n_*$, with no large-$N$ clause.
--
--   **Formalization Note** $c$ depends only on $k,r,\theta$ and is chosen before $N$, the partition, the algorithm, $\ell$ and $T$. $a^*_{r,\ell}$ is written with the full counter $C_r$ (equal to $C^*_r$ by (4.3)).
--
--   Differences from the source:
--   - encoding: a*_{r,ℓ}(T) = ‖P*_{r,ℓ} ζ_T‖ with the eligible counter C*_r → dbAmp b r ℓ (A.compressedState T) with the full counter C_r; reason: C*_r = C_r pointwise, (4.3) p.35; same value on every database
--   - reading: there is a constant c_{k,r,θ} > 0 such that, for every type … → ∃ c > 0 chosen before N, the partition, its type, the algorithm, ℓ and T; reason: the subscripts say c depends on k, r, θ only
--   - encoding: public buckets of exact type λ = (1^{n_1}, …, k^{n_k}), N = Σ i n_i, h = Σ n_i → n : ℕ → ℕ read at 1..k and HasBucketType b k n; reason: the bucket condition forces N = Σ i n_i and h = Σ n_i; same instances
--   - encoding: forward compressed-query algorithms with arbitrary auxiliary registers; U_{s+1} applied after query s+1; ζ_s → MultiCollQ.FwdAlg with any finite register Wk; A.Uop s (0-based); A.compressedState s, with U_0 absorbed into init; reason: deferred measurement and purification (base FwdAlg); same class of algorithms and the same states
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), Theorem 4.6, p.41, eqs. (4.25), (4.26)

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_MultiCollQ_Aconst
import Definitions.Def_MultiCollQ_FwdAlg
import Definitions.Def_MultiCollQ_Supplement_tauScale

namespace MultiCollQ.Supplement

open CompPermOracle

/-- Theorem 4.6 (Exponential database tail for all target counts) (Peng, Hou, Dong, *Quantum
multi-collision lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), p.41). Fix
`k ≥ r ≥ 2` (§4.1, p.34) and `θ ∈ (0, 1)`. There is a constant `c_{k,r,θ} > 0` such that, for every
type with `n_* ≥ 1` and every integer `1 ≤ ℓ ≤ n_*`, `a*_{r,ℓ}(T) ≤ θ^ℓ` whenever
`0 ≤ T ≤ c_{k,r,θ} τ_{r,ℓ}(N, n_*)` (4.26). The query count `T` is an integer.

**Formalization Note.** `c` depends only on `k, r, θ` and is chosen before `N`, the bucket
partition and its type, the algorithm, `ℓ` and `T`; there is no large-`N` clause. The buckets are
`b : Fin N → Fin h` with `HasBucketType b k n`, `n_* = nStar k r n`. `a*_{r,ℓ}(T)` is
`dbAmp b r ℓ (A.compressedState T)` (`C*_r = C_r` pointwise, (4.3)) for an arbitrary forward
compressed-query algorithm with any finite auxiliary register. `τ_{r,ℓ}(N, n_*)` is
`tauScale r ℓ N n_*` (4.25). -/
theorem theorem_4_6 (k r : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ {N h : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk]
      (b : Fin N → Fin h) (n : ℕ → ℕ), HasBucketType b k n → 1 ≤ nStar k r n →
      ∀ (A : FwdAlg N Wk) (ℓ T : ℕ), 1 ≤ ℓ → ℓ ≤ nStar k r n →
        (T : ℝ) ≤ c * tauScale r ℓ N (nStar k r n) →
        dbAmp b r ℓ (A.compressedState T) ≤ θ ^ ℓ := by sorry

end MultiCollQ.Supplement
