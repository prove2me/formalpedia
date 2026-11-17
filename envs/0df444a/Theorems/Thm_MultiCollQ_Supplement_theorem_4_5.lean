-- Prove2me | Theorems.Thm_MultiCollQ_Supplement_theorem_4_5
-- name    : MultiCollQ.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:01:06.63769+00:00
-- url     : https://prove2.me/theorems/5cbd9ed0-6a89-4cf4-81f9-1bb50c5177cf
-- title:
--   Theorem 4.5 — finite bound (4.19) by simultaneous truncation
-- statement:
--   Fix $k\ge r\ge2$ and public buckets of exact type $\lambda=(1^{n_1},\dots,k^{n_k})$ with $n_*=\sum_{i=r}^kn_i\ge1$, and let $1\le\ell\le n_*$ (the standing assumptions of §4.1). Let $a^*_{r,\ell}(T)$ be the norm of the component of the joint state after $T$ compressed queries whose database has at least $\ell$ eligible buckets with $r$ recorded images. Let $L_0=n_*$ and choose nonnegative integer cutoffs $L_1,\dots,L_{r-1}$. For every forward compressed-query algorithm and every integer $1\le T<N$,
--
--   $$
--   a^*_{r,\ell}(T)\le F_{r,\ell}(T,L_{r-1})+\sum_{j=1}^{r-1}F_{j,L_j+1}(T,L_{j-1}), \tag{4.19}
--   $$
--
--   where $F_{j,m}(s,L)$ is the truncated-trajectory bound (4.17) with $d=N-T$ and $c_j=\sqrt{8(k-j+1)}$. No monotonicity assumption on the cutoffs is required.
--
--   The first term bounds the target amplitude of the trajectory truncated at every intermediate level, and the remaining $r-1$ terms bound the leakage through each cutoff, summed over time.
--
--   **Formalization Note** $a^*_{r,\ell}$ is written with the full counter $C_r$, since $C^*_r=C_r$ pointwise (4.3); the cutoffs are a function $L:\mathbb N\to\mathbb N$ of which only $L_1,\dots,L_{r-1}$ are read.
--
--   Differences from the source:
--   - encoding: a*_{r,ℓ}(T) = ‖P*_{r,ℓ} ζ_T‖ with the eligible counter C*_r → dbAmp b r ℓ (A.compressedState T) with the full counter C_r; reason: C*_r = C_r pointwise, (4.3) p.35: a bucket with at least r recorded images has size at least r; same value on every database
--   - encoding: public buckets of exact type λ = (1^{n_1}, …, k^{n_k}), N = Σ i n_i, h = Σ n_i → n : ℕ → ℕ read at 1..k and HasBucketType b k n; reason: the bucket condition forces N = Σ i n_i and h = Σ n_i; same instances
--   - encoding: cutoffs L_1, …, L_{r−1} with L_0 = n_* → L : ℕ → ℕ, of which only L 1, …, L (r−1) are read; L_0 is nStar k r n; reason: same choices of cutoffs
--   - encoding: forward compressed-query algorithms with arbitrary auxiliary registers; U_{s+1} applied after query s+1; ζ_s → MultiCollQ.FwdAlg with any finite register Wk; A.Uop s (0-based); A.compressedState s, with U_0 absorbed into init; reason: deferred measurement and purification (base FwdAlg); same class of algorithms and the same states
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), Theorem 4.5, pp.39–40, eq. (4.19); setting §4.1, pp.34–35

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_MultiCollQ_Aconst
import Definitions.Def_MultiCollQ_FwdAlg
import Definitions.Def_MultiCollQ_Supplement_FTrunc
import Definitions.Def_MultiCollQ_Supplement_tauScale

namespace MultiCollQ.Supplement

open CompPermOracle

/-- Theorem 4.5 (Finite bound by simultaneous truncation) (Peng, Hou, Dong, *Quantum multi-collision
lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), pp.39–40). Fix `k ≥ r ≥ 2` and an
exact type `λ = (1^{n_1}, …, k^{n_k})` of the public buckets, with `n_* = Σ_{i=r}^k n_i ≥ 1` and
`1 ≤ ℓ ≤ n_*` (§4.1, pp.34–35). Let `L_0 = n_*` and choose nonnegative integer cutoffs
`L_1, …, L_{r−1}`. For every forward compressed-query algorithm and `1 ≤ T < N`,
`a*_{r,ℓ}(T) ≤ F_{r,ℓ}(T, L_{r−1}) + Σ_{j=1}^{r−1} F_{j,L_j+1}(T, L_{j−1})` (4.19). No monotonicity
assumption on the cutoffs is required.

**Formalization Note.** The buckets are `b : Fin N → Fin h` with `HasBucketType b k n` (size
multiset `λ`). `a*_{r,ℓ} = ‖P*_{r,ℓ} ζ_T‖` is `dbAmp b r ℓ (A.compressedState T)`, since
`C*_r = C_r` pointwise (4.3): a bucket with at least `r` recorded images has size at least `r`.
The cutoffs are a function `L : ℕ → ℕ` of which only `L 1, …, L (r−1)` are read; `L_0 = n_*` is
`Lc 0`. `F_{j,m}(s, L)` is `FTrunc k N T j m s L` (4.17), with `d = N − T` in every term. -/
theorem theorem_4_5 {N h k r ℓ T : ℕ} {n : ℕ → ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk]
    (b : Fin N → Fin h) (hb : HasBucketType b k n) (hr : 2 ≤ r) (hrk : r ≤ k)
    (hn : 1 ≤ nStar k r n) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ nStar k r n) (L : ℕ → ℕ)
    (A : FwdAlg N Wk) (hT : 1 ≤ T) (hTN : T < N) :
    let Lc : ℕ → ℕ := fun j => if j = 0 then nStar k r n else L j
    dbAmp b r ℓ (A.compressedState T) ≤
      FTrunc k N T r ℓ T (Lc (r - 1)) +
        ∑ j ∈ Finset.Icc 1 (r - 1), FTrunc k N T j (Lc j + 1) T (Lc (j - 1)) := by sorry

end MultiCollQ.Supplement
