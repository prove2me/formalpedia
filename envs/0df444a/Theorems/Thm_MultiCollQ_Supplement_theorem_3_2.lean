-- Prove2me | Theorems.Thm_MultiCollQ_Supplement_theorem_3_2
-- name    : MultiCollQ.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:59:20.279478+00:00
-- url     : https://prove2.me/theorems/80eb92c7-a733-4c9a-9b54-d6d9062b45ba
-- title:
--   Theorem 3.2 — one-step transition bound (3.7) and query recurrence (3.8)
-- statement:
--   Partition $[N]$ into public buckets of sizes at most $k$, let $C_j(D)$ be the number of buckets holding at least $j$ images of the database $D$, $P_{j,m}=\mathbf 1\{C_j\ge m\}$, and $a_{j,m}(s)=\|P_{j,m}\zeta_s\|$ for the joint state $\zeta_s$ of a forward compressed-query algorithm after $s$ queries. Let $2\le r\le k$, let $\ell\ge1$ and $L\ge\ell-1$ be integers, and let $0\le s<N$. Define
--
--   $$
--   G=\mathbf 1\{C_r=\ell-1,\ C_{r-1}\le L\},\qquad R=\mathbf 1\{C_r=\ell-1,\ C_{r-1}\ge L+1\},\qquad \gamma=c_r\sqrt{\frac{L-\ell+1}{N-s}},
--   $$
--
--   with $c_r=\sqrt{8(k-r+1)}$. For every vector $v$ (not necessarily normalized) supported on databases of size at most $s$,
--
--   $$
--   \|P_{r,\ell}U_{s+1}\mathsf{cpO}\,v\|\le\|P_{r,\ell}v\|+\gamma\|Gv\|+\|Rv\|\le\|P_{r,\ell}v\|+\gamma\|P_{r,\ell-1}v\|+\|P_{r-1,L+1}v\|. \tag{3.7}
--   $$
--
--   In particular, since $\zeta_{s+1}=U_{s+1}\mathsf{cpO}\,\zeta_s$,
--
--   $$
--   a_{r,\ell}(s+1)\le a_{r,\ell}(s)+\gamma\,a_{r,\ell-1}(s)+a_{r-1,L+1}(s). \tag{3.8}
--   $$
--
--   This is the one-query step of the paper's recursive argument: it controls how much target amplitude a single compressed query can create from databases just below the threshold, splitting them into a good part (few $(r-1)$-collisions) and a bad part handled by the next level down.
--
--   **Formalization Note** $U_{s+1}$ is the algorithm's unitary after query $s+1$ (`A.Uop s`, 0-based), acting as the identity on the database; $\mathsf{cpO}$ is `MultiCollQ.cpStep`. The three parts are stated as one conjunction, with (3.7) for every $v$ and (3.8) for every algorithm.
--
--   Differences from the source:
--   - encoding: [N] and public buckets Q_1, …, Q_h → Fin N (0-based) and a bucket map b : Fin N → Fin h with Q_c = b⁻¹(c); reason: Lean convention; same instances
--   - encoding: forward compressed-query algorithms with arbitrary auxiliary registers; U_{s+1} applied after query s+1; ζ_s → MultiCollQ.FwdAlg with any finite register Wk; A.Uop s (0-based); A.compressedState s, with U_0 absorbed into init; reason: deferred measurement and purification (base FwdAlg); same class of algorithms and the same states
--   - encoding: buckets of size at most k (§3, p.18; p.21) → BucketsBounded b k (sizes in [1, k]); reason: blocks of a partition are nonempty; same instances
--   - encoding: v supported on databases of size at most s → v (c, D) = 0 whenever s < size D; reason: the definition of support, coordinatewise
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), Theorem 3.2, pp.21–22, eqs. (3.7), (3.8)

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_MultiCollQ_Aconst
import Definitions.Def_MultiCollQ_FwdAlg
import Definitions.Def_MultiCollQ_Supplement_dbNorm

namespace MultiCollQ.Supplement

open CompPermOracle

/-- Theorem 3.2 (One-step transition bound and query recurrence) (Peng, Hou, Dong, *Quantum
multi-collision lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), pp.21–22). For
public buckets of sizes at most `k`, let `2 ≤ r ≤ k`, let `ℓ ≥ 1` and `L ≥ ℓ − 1` be integers and
`0 ≤ s < N`. Put `G = 1{C_r = ℓ−1, C_{r−1} ≤ L}`, `R = 1{C_r = ℓ−1, C_{r−1} ≥ L+1}` and
`γ = c_r √((L − ℓ + 1)/(N − s))`. For every (not necessarily normalized) vector `v` supported on
databases of size at most `s`,
`‖P_{r,ℓ} U_{s+1} cpO v‖ ≤ ‖P_{r,ℓ} v‖ + γ‖Gv‖ + ‖Rv‖ ≤ ‖P_{r,ℓ} v‖ + γ‖P_{r,ℓ−1} v‖ + ‖P_{r−1,L+1} v‖`
(3.7), and in particular `a_{r,ℓ}(s+1) ≤ a_{r,ℓ}(s) + γ a_{r,ℓ−1}(s) + a_{r−1,L+1}(s)` (3.8).

**Formalization Note.** Buckets are `b : Fin N → Fin h` with sizes in `[1, k]`
(`BucketsBounded b k`, §3, p.18 and p.21). `U_{s+1}`, the algorithm's unitary after query `s+1`, is
`A.Uop s` (0-based), acting as `U ⊗ I` on the database (`opTensor (A.Uop s) 1`); `cpO` is
`MultiCollQ.cpStep`. `‖P_{j,m} v‖` is `dbAmp b j m v` and `‖1_S v‖` is `dbNorm S v`. "Supported on
databases of size at most `s`" is `v(c, D) = 0` whenever `|D| > s`. `ζ_s` is
`A.compressedState s`, so `ζ_{s+1} = (U_s ⊗ I) cpO ζ_s` by definition. `ℓ − 1` and `r − 1` are
natural subtraction with `ℓ ≥ 1`, `r ≥ 2`; `γ` is computed in `ℝ`. -/
theorem theorem_3_2 {N h k r ℓ L s : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk]
    (b : Fin N → Fin h) (hb : BucketsBounded b k) (hr : 2 ≤ r) (hrk : r ≤ k) (hℓ : 1 ≤ ℓ)
    (hL : ℓ - 1 ≤ L) (hs : s < N) (A : FwdAlg N Wk) :
    let γ : ℝ := cConst k r * Real.sqrt (((L : ℝ) - ℓ + 1) / ((N : ℝ) - s))
    let G : PartialPerm N → Prop := fun D => levelCount b r D = ℓ - 1 ∧ levelCount b (r - 1) D ≤ L
    let R : PartialPerm N → Prop := fun D => levelCount b r D = ℓ - 1 ∧ L + 1 ≤ levelCount b (r - 1) D
    (∀ v : Hil (FAcc N Wk × PartialPerm N), (∀ c D, s < size D → v (c, D) = 0) →
      dbAmp b r ℓ (opTensor (A.Uop s) (1 : Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N))
          (cpStep v)) ≤ dbAmp b r ℓ v + γ * dbNorm G v + dbNorm R v ∧
      dbAmp b r ℓ v + γ * dbNorm G v + dbNorm R v ≤
        dbAmp b r ℓ v + γ * dbAmp b r (ℓ - 1) v + dbAmp b (r - 1) (L + 1) v) ∧
    dbAmp b r ℓ (A.compressedState (s + 1)) ≤
      dbAmp b r ℓ (A.compressedState s) + γ * dbAmp b r (ℓ - 1) (A.compressedState s) +
        dbAmp b (r - 1) (L + 1) (A.compressedState s) := by sorry

end MultiCollQ.Supplement
