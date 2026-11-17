-- Prove2me | Theorems.Thm_MultiCollQ_Supplement_theorem_3_8
-- name    : MultiCollQ.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:59:52.106643+00:00
-- url     : https://prove2.me/theorems/d8420dff-6023-4f8f-9f4d-bc18c55f830a
-- title:
--   Theorem 3.8 — exponential tail $a_{r,\ell}(T)\le\theta^\ell$ for the pure type at the query threshold
-- statement:
--   Fix $2\le r\le k$ and $\theta\in(0,1)$, and let $N=kn$ with public buckets of the pure type $(k^n)$ ($n$ buckets of size $k$). There is a constant $c_{k,r,\theta}>0$ such that, for sufficiently large $N$, every forward compressed-query algorithm satisfies
--
--   $$
--   a_{r,\ell}(T)\le\theta^{\ell}
--   $$
--
--   for every integer $1\le\ell\le n$ and every nonnegative integer $T$ with
--
--   $$
--   T\le c_{k,r,\theta}\,\ell^{1/\alpha_r}N^{\beta_r/\alpha_r}, \tag{3.25}
--   $$
--
--   where $\alpha_r=2-2^{1-r}$, $\beta_r=1-2^{1-r}$ and $a_{r,\ell}(T)$ is the norm of the component of the joint state after $T$ compressed queries whose database has at least $\ell$ buckets with $r$ recorded images.
--
--   The first-moment bound only gives $a_{r,\ell}(T)^2=O(1)$ at the query threshold; this theorem upgrades it to decay exponential in the number $\ell$ of target buckets.
--
--   **Formalization Note** "There is a constant … for sufficiently large $N$" is stated as: there are $c>0$ and $N_0$, depending only on $k,r,\theta$, such that for every $n$ with $kn\ge N_0$, every bucket map of type $(k^n)$, every algorithm (any finite auxiliary register), every $\ell$ and every $T$ the bound holds.
--
--   Differences from the source:
--   - reading: there is a constant c_{k,r,θ} > 0 such that, for sufficiently large N → ∃ c > 0, ∃ N₀, both chosen before n, the buckets, the algorithm, ℓ and T; reason: the subscripts say c depends on k, r, θ only; the uniform reading is the stronger one
--   - encoding: pure type (k^n), N = kn → b : Fin (k * n) → Fin h with HasBucketType b k (pureType k n); reason: forces h = n and every bucket of size k; same instances
--   - encoding: forward compressed-query algorithms with arbitrary auxiliary registers; U_{s+1} applied after query s+1; ζ_s → MultiCollQ.FwdAlg with any finite register Wk; A.Uop s (0-based); A.compressedState s, with U_0 absorbed into init; reason: deferred measurement and purification (base FwdAlg); same class of algorithms and the same states
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), Theorem 3.8, p.31, eq. (3.25)

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_levelCount
import Definitions.Def_MultiCollQ_Aconst
import Definitions.Def_MultiCollQ_FwdAlg
import Definitions.Def_MultiCollQ_HasExactType

namespace MultiCollQ.Supplement

open CompPermOracle

/-- Theorem 3.8 (An exponential tail at the database query threshold) (Peng, Hou, Dong, *Quantum
multi-collision lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), p.31). Fix
`2 ≤ r ≤ k` and `θ ∈ (0, 1)`, and let `N = kn`. There is a constant `c_{k,r,θ} > 0` such that, for
sufficiently large `N`, `a_{r,ℓ}(T) ≤ θ^ℓ` for every integer `1 ≤ ℓ ≤ n` and every nonnegative
integer `T ≤ c_{k,r,θ} ℓ^{1/α_r} N^{β_r/α_r}` (3.25).

**Formalization Note.** "There is a constant … for sufficiently large `N`" is pinned as `∃ c > 0`,
`∃ N₀`, both depending only on `k, r, θ` and chosen before `n`, the buckets, the algorithm, `ℓ` and
`T`. The pure type `(k^n)` is public buckets `b : Fin (k n) → Fin h` with
`HasBucketType b k (pureType k n)` (then `h = n` and every bucket has size `k`). `a_{r,ℓ}(T)` is
`dbAmp b r ℓ (A.compressedState T)` for an arbitrary forward compressed-query algorithm `A` with
any finite auxiliary register `Wk`. `α_r = 2 − 2^{1−r}`, `β_r = 1 − 2^{1−r}`; real powers. -/
theorem theorem_3_8 (k r : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ {n h : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk]
      (b : Fin (k * n) → Fin h), HasBucketType b k (pureType k n) → N₀ ≤ k * n →
      ∀ (A : FwdAlg (k * n) Wk) (ℓ T : ℕ), 1 ≤ ℓ → ℓ ≤ n →
        (T : ℝ) ≤ c * (ℓ : ℝ) ^ (1 / alphaExp r) * ((k * n : ℕ) : ℝ) ^ (betaExp r / alphaExp r) →
        dbAmp b r ℓ (A.compressedState T) ≤ θ ^ ℓ := by sorry

end MultiCollQ.Supplement
