-- Prove2me | Theorems.Thm_MultiCollQ_upper_bound
-- name    : MultiCollQ.upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:45.483272+00:00
-- url     : https://prove2.me/theorems/07efbb7d-512c-489c-ab97-d608545e4e58
-- title:
--   Proof of Theorem 1.1 (upper bound) — $O_{k,r}(\ell^{2^{r-1}/(2^r-1)}N^{(2^{r-1}-1)/(2^r-1)})$ queries find $\ell$ $r$-collisions on every function of type $(k^n)$
-- statement:
--   Fix $k\ge r\ge2$ and put $N=kn$. There are $C>0$ and $N_0$, depending only on $k,r$, such that for every $n$ with $N\ge N_0$, every alphabet size $q\ge n$ and every integer $1\le\ell\le N^{2^{-r}}$, some quantum algorithm making at most
--
--   $$
--   C\,\ell^{2^{r-1}/(2^r-1)}N^{(2^{r-1}-1)/(2^r-1)}
--   $$
--
--   phase queries finds $r$-collisions in $\ell$ distinct equality classes with probability at least $2/3$ on **every** function $[kn]\to\mathbb Z_q$ of exact type $(k^n)$.
--
--   This is the upper half of Theorem 1.1, obtained from a multi-target version of the Liu–Zhandry construction.
--
--   **Formalization Note** The algorithm is a `QAlgorithms.QueryAlg` with the phase oracle, any finite workspace, and an output map to $\ell$ groups of $r$ inputs; it makes exactly $T\le C\tau$ queries.
--
--   Differences from the source:
--   - reading: the total worst-case query count is $O_{k,r}(\ell^{2^{r-1}/(2^r-1)}N^{(2^{r-1}-1)/(2^r-1)})$, with a bound independent of $q$, for sufficiently large $N$ → $\exists C>0,\ \exists N_0$ (depending on $k,r$) chosen before $n,q,\ell$, with an algorithm of $T\le C\tau$ queries; reason: the standard meaning of $O_{k,r}$, uniform over $q$ and the range of $\ell$ (Theorem 1.1)
--   - encoding: the algorithm models (start state and unitaries independent of the oracle, measurement of the output register) → `QAlgorithms.QueryAlg` with the phase oracle and an output map to $\ell$ groups of $r$ inputs; reason: same class of algorithms
--   - encoding: $[N]$, $\mathbb Z_q$ → `Fin N` (0-based), `ZMod q` with `[NeZero q]`; reason: Lean convention; same instances ($q\ge n\ge1$ once $N_0\ge1$)
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Proof of Theorem 1.1, upper bound, §3.3, p.27

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_MultiCollQ_HasExactType
import Definitions.Def_MultiCollQ_collisionRel

namespace MultiCollQ

open QAlgorithms

/-- Proof of Theorem 1.1, upper bound (Peng, Hou, Dong, manuscript (Oct. 2026), §3.3, p.27): the
multi-target Liu–Zhandry construction. Fix `k ≥ r ≥ 2`. There are `C > 0` and `N₀` depending only
on `k, r` such that for every `n` with `N = kn ≥ N₀`, every alphabet size `q ≥ n` and every integer
`1 ≤ ℓ ≤ N^{2^{−r}}`, some algorithm making at most
`C ℓ^{2^{r−1}/(2^r−1)} N^{(2^{r−1}−1)/(2^r−1)}` phase queries finds `ℓ` `r`-collisions in distinct
equality classes with probability at least `2/3` on **every** function of exact type `(k^n)`.

**Formalization Note.** The algorithm is `QAlgorithms.QueryAlg` (any finite workspace) with the phase
oracle (2.1) and an output map to `ℓ` groups of `r` inputs; it makes exactly `T` queries with
`T ≤ C·τ`. `C` and `N₀` are chosen before `n, q, ℓ`, so the bound is independent of `q`. Real
powers; `r − 1` is natural subtraction with `r ≥ 2`. `[NeZero q]` excludes only `q = 0`. -/
theorem upper_bound (k r : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ (n q : ℕ) [NeZero q] (ℓ : ℕ),
      N₀ ≤ k * n → n ≤ q → 1 ≤ ℓ → (ℓ : ℝ) ≤ ((k * n : ℕ) : ℝ) ^ ((2 : ℝ) ^ (-(r : ℝ))) →
      ∃ (wb T : ℕ) (A : QueryAlg (Fin (k * n)) (ZMod q) (Fin wb) T)
        (out : (Fin (k * n) × ZMod q) × Fin wb → (Fin ℓ → Fin r → Fin (k * n))),
        (T : ℝ) ≤ C * ((ℓ : ℝ) ^ ((2 : ℝ) ^ (r - 1) / ((2 : ℝ) ^ r - 1)) *
            ((k * n : ℕ) : ℝ) ^ (((2 : ℝ) ^ (r - 1) - 1) / ((2 : ℝ) ^ r - 1))) ∧
        ∀ f ∈ exactTypeSet (k * n) q k (pureType k n),
          2 / 3 ≤ SelectiveDPT.successProb A out (collisionRel r ℓ) f := by sorry

end MultiCollQ
