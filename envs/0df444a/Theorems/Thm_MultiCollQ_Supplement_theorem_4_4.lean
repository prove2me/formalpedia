-- Prove2me | Theorems.Thm_MultiCollQ_Supplement_theorem_4_4
-- name    : MultiCollQ.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:00:29.504668+00:00
-- url     : https://prove2.me/theorems/9d3b266b-bdbb-4c41-bc19-386b3898cf03
-- title:
--   Theorem 4.4 — function-query lower bound $\Omega(\tau_{r,\ell}(N,n_*))$ for arbitrary exact types
-- statement:
--   Fix constants $k\ge r\ge2$ and $p_0\in(0,1)$. For an exact type $\lambda=(1^{n_1},\dots,k^{n_k})$ write $N=\sum_{i=1}^k in_i$, $h=\sum_{i=1}^kn_i$ and $n_*=\sum_{i=r}^kn_i$. For sufficiently large $N$, uniformly over all exact types with $n_*\ge1$, all alphabet sizes $q\ge h$ and all integers
--
--   $$
--   1\le\ell\le n_*^{2^{-r}}, \tag{4.14}
--   $$
--
--   any quantum algorithm that, for every function $f:[N]\to\mathbb Z_q$ of exact type $\lambda$, finds $r$-collisions in $\ell$ distinct equality classes with probability at least $p_0$ requires
--
--   $$
--   \Omega_{k,r,p_0}\Bigl(\frac{\sqrt N\,\ell^{1/(2-2^{1-r})}}{n_*^{1/(2^{r+1}-2)}}\Bigr) \tag{4.15}
--   $$
--
--   queries to the phase oracle $O_f|x,c\rangle=\omega_q^{c f(x)}|x,c\rangle$ in the worst case.
--
--   This extends the lower bound of the base mission from the pure type $(k^n)$ to every exact type; only the eligible classes (of size at least $r$) enter the scale.
--
--   **Formalization Note** $\Omega_{k,r,p_0}$ with "sufficiently large $N$" is stated as: there are $c>0$ and $N_0$, depending only on $k,r,p_0$, such that for every $N\ge N_0$, every type with $N=\sum_i in_i$, every $q\ge h$, every $\ell$ in range, every algorithm with $t$ queries (any finite workspace, computational-basis measurement and output map) whose success probability is at least $p_0$ on every function of type $\lambda$ has $t\ge c\,\tau_{r,\ell}(N,n_*)$.
--
--   Differences from the source:
--   - reading: Ω_{k,r,p_0}(…) for sufficiently large N, uniformly over types, q and ℓ → ∃ c > 0, ∃ N₀ depending on k, r, p₀ only, then ∀ N ≥ N₀, type, q, ℓ, algorithm: t ≥ c·τ_{r,ℓ}(N, n_*); reason: the stated uniformity; the stronger reading
--   - encoding: exact type λ with N = Σ i n_i, h = Σ n_i → n : ℕ → ℕ read at 1..k, hypothesis N = Σ_{i=1}^k i n_i, h written as Σ_{i=1}^k n_i; reason: same instances
--   - encoding: quantum algorithms with phase queries O_f, worst-case success probability → QAlgorithms.QueryAlg on Fin N × ZMod q with workspace Fin wb, an output map, SelectiveDPT.successProb ≥ p₀ for every f ∈ exactTypeSet; reason: same class of algorithms as the base goal
--   - encoding: [N], Z_q → Fin N (0-based), ZMod q with [NeZero q]; reason: Lean convention; q ≥ h ≥ n_* ≥ 1 on the range used
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), Theorem 4.4, p.38, eqs. (4.14), (4.15)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_MultiCollQ_HasExactType
import Definitions.Def_MultiCollQ_collisionRel
import Definitions.Def_MultiCollQ_Supplement_tauScale

namespace MultiCollQ.Supplement

open QAlgorithms

/-- Theorem 4.4 (Function-query lower bound for arbitrary types) (Peng, Hou, Dong, *Quantum
multi-collision lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), p.38). Fix
constants `k ≥ r ≥ 2` and `p₀ ∈ (0, 1)`. For sufficiently large `N`, uniformly over all exact types
`λ = (1^{n_1}, …, k^{n_k})` with `n_* = Σ_{i=r}^k n_i ≥ 1`, all `q ≥ h` and all integers
`1 ≤ ℓ ≤ n_*^{2^{−r}}` (4.14), any quantum algorithm that, for every function `f` of exact type `λ`,
finds `r`-collisions in `ℓ` distinct equality classes with probability at least `p₀` requires
`Ω_{k,r,p₀}(√N ℓ^{1/(2−2^{1−r})} / n_*^{1/(2^{r+1}−2)})` (4.15) queries to `O_f` in the worst case.

**Formalization Note.** `Ω_{k,r,p₀}` with "sufficiently large `N`, uniformly over types" is pinned as
`∃ c > 0, ∃ N₀` depending only on `k, r, p₀`, chosen before `N`, the type, `q` and `ℓ`. The type is
`n : ℕ → ℕ` read at `1 ≤ i ≤ k`, with `N = Σ_{i=1}^k i n_i` and `h = Σ_{i=1}^k n_i` (§4.1, (4.1));
`F_{λ,q}` is `exactTypeSet N q k n`. Algorithms are `QAlgorithms.QueryAlg` with any finite workspace
`Fin wb`, `t` phase queries `O_f|x, c⟩ = ω_q^{c f(x)}|x, c⟩` (2.1), a computational-basis measurement
and an output map to `ℓ` groups of `r` inputs (`SelectiveDPT.successProb`, `collisionRel`). The
premise is worst-case: success at least `p₀` on every `f` of type `λ`. `[NeZero q]` excludes only
`q = 0` (excluded anyway by `q ≥ h ≥ n_* ≥ 1`). The scale is `tauScale r ℓ N n_*` (4.25); real
powers. -/
theorem theorem_4_4 (k r : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hp₁ : p₀ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (N q : ℕ) [NeZero q] (n : ℕ → ℕ) (ℓ : ℕ),
      N₀ ≤ N → N = ∑ i ∈ Finset.Icc 1 k, i * n i → ∑ i ∈ Finset.Icc 1 k, n i ≤ q →
      1 ≤ nStar k r n → 1 ≤ ℓ → (ℓ : ℝ) ≤ (nStar k r n : ℝ) ^ ((2 : ℝ) ^ (-(r : ℝ))) →
      ∀ (wb t : ℕ) (A : QueryAlg (Fin N) (ZMod q) (Fin wb) t)
        (out : (Fin N × ZMod q) × Fin wb → (Fin ℓ → Fin r → Fin N)),
        (∀ f ∈ exactTypeSet N q k n, p₀ ≤ SelectiveDPT.successProb A out (collisionRel r ℓ) f) →
        c * tauScale r ℓ N (nStar k r n) ≤ t := by sorry

end MultiCollQ.Supplement
