-- Prove2me | Theorems.Thm_MultiCollQ_corollary_3_6
-- name    : MultiCollQ.corollary_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:57.921196+00:00
-- url     : https://prove2.me/theorems/9097718f-d6ac-4f8c-ada4-f94185a8159f
-- title:
--   Corollary 3.6 — finding $\ell$ $r$-collisions with average success $p_0$ needs $\Omega_{k,r,p_0}(\ell^{1/\alpha_r}N^{\beta_r/\alpha_r})$ queries
-- statement:
--   Fix $k\ge r\ge2$, put $N=kn$, and fix $p_0\in(0,1)$. There are $c>0$ and $N_0$, depending only on $k,r,p_0$, such that for every $n$ with $N\ge N_0$, every alphabet size $q\ge n$ and every integer
--
--   $$
--   1\le\ell\le N^{2^{-r}},
--   $$
--
--   every algorithm making $t$ phase queries to $O_f$ that finds $\ell$ $r$-tuples in distinct equality classes with success probability at least $p_0$, averaged over the uniform distribution on functions $[kn]\to\mathbb Z_q$ of exact type $(k^n)$, satisfies
--
--   $$
--   t\ge c\,\ell^{1/\alpha_r}N^{\beta_r/\alpha_r},\qquad \frac1{\alpha_r}=\frac{2^{r-1}}{2^r-1},\quad\frac{\beta_r}{\alpha_r}=\frac{2^{r-1}-1}{2^r-1}.
--   $$
--
--   The constant is independent of $q$. This is the distributional lower bound; Theorem 1.1's worst-case lower bound is its case $p_0=2/3$.
--
--   **Formalization Note** Algorithms are `QAlgorithms.QueryAlg` with any finite workspace and the phase oracle; outputs are $\ell$ groups of $r$ inputs.
--
--   Differences from the source:
--   - reading: $t=\Omega_{k,r,p_0}(\ell^{1/\alpha_r}N^{\beta_r/\alpha_r})$ with the implicit constant independent of $q$ → $\exists c>0,\ \exists N_0$ (depending on $k,r,p_0$) chosen before $n,q,\ell$, with $t\ge c\,\ell^{1/\alpha_r}N^{\beta_r/\alpha_r}$ whenever $kn\ge N_0$; reason: the standard meaning of $\Omega$ as $N\to\infty$ (the proof's "for sufficiently large $N$"), uniform over $q$ and the range of $\ell$
--   - encoding: the algorithm models (start state and unitaries independent of the oracle, measurement of the output register) → `QAlgorithms.QueryAlg` with the phase oracle and an output map to $\ell$ groups of $r$ inputs; reason: same class of algorithms
--   - encoding: $[N]$, $\mathbb Z_q$ → `Fin N` (0-based), `ZMod q` with `[NeZero q]`; reason: Lean convention; same instances ($q\ge n\ge1$ once $N_0\ge1$)
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Corollary 3.6, (3.16)–(3.17), p.26 (proof pp.26–27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_MultiCollQ_HasExactType
import Definitions.Def_MultiCollQ_collisionRel
import Definitions.Def_MultiCollQ_Aconst

namespace MultiCollQ

open QAlgorithms

/-- Corollary 3.6 (Multi-collision query lower bound) (Peng, Hou, Dong, manuscript (Oct. 2026),
p.26). Fix `k ≥ r ≥ 2` and `p₀ ∈ (0, 1)`. There are `c > 0` and `N₀` depending only on `k, r, p₀`
such that for every `n` with `N = kn ≥ N₀`, every alphabet size `q ≥ n` and every integer
`1 ≤ ℓ ≤ N^{2^{−r}}` (3.16), every algorithm making `t` phase queries to `O_f` that finds `ℓ`
`r`-tuples in distinct equality classes with success probability at least `p₀` under the uniform
distribution on functions of exact type `(k^n)` has `t ≥ c ℓ^{1/α_r} N^{β_r/α_r}` (3.17).

**Formalization Note.** `Ω_{k,r,p₀}` is pinned as `∃ c > 0, ∃ N₀` chosen before `n, q, ℓ`, so the
constant is independent of `q` and `ℓ`. `1/α_r = 2^{r−1}/(2^r − 1)` and
`β_r/α_r = (2^{r−1} − 1)/(2^r − 1)`. `[NeZero q]` (to make `ZMod q` finite) excludes only `q = 0`,
which `q ≥ n ≥ 1` excludes for `N₀ ≥ 1`. Algorithms are `QAlgorithms.QueryAlg` with any finite
workspace and the phase oracle (2.1). -/
theorem corollary_3_6 (k r : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hp₁ : p₀ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (n q : ℕ) [NeZero q] (ℓ : ℕ),
      N₀ ≤ k * n → n ≤ q → 1 ≤ ℓ → (ℓ : ℝ) ≤ ((k * n : ℕ) : ℝ) ^ ((2 : ℝ) ^ (-(r : ℝ))) →
      ∀ (wb t : ℕ) (A : QueryAlg (Fin (k * n)) (ZMod q) (Fin wb) t)
        (out : (Fin (k * n) × ZMod q) × Fin wb → (Fin ℓ → Fin r → Fin (k * n))),
        p₀ ≤ avgSuccess (exactTypeSet (k * n) q k (pureType k n)) A out (collisionRel r ℓ) →
        c * (ℓ : ℝ) ^ (1 / alphaExp r) * ((k * n : ℕ) : ℝ) ^ (betaExp r / alphaExp r) ≤ t := by sorry

end MultiCollQ
