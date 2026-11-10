-- Prove2me | Theorems.Thm_MultiCollQ_theorem_1_1_tight_collision_bound
-- name    : MultiCollQ.theorem_1_1_tight_collision_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:05.558201+00:00
-- url     : https://prove2.me/theorems/9afe4203-b05d-45c4-9031-ca6f6f1c2b27
-- title:
--   Theorem 1.1 — finding $\ell$ $r$-collisions in a function of exact type $(k^n)$ takes $\Theta_{k,r}(\ell^{2^{r-1}/(2^r-1)}N^{(2^{r-1}-1)/(2^r-1)})$ quantum queries
-- statement:
--   Fix constants $k\ge r\ge2$ and let $N=kn$. Put
--
--   $$
--   \tau=\ell^{2^{r-1}/(2^r-1)}N^{(2^{r-1}-1)/(2^r-1)} .
--   $$
--
--   There are constants $c,C>0$ and $N_0$, depending only on $k$ and $r$, such that for every $n$ with $N\ge N_0$, every alphabet size $q\ge n$ and every integer $1\le\ell\le N^{2^{-r}}$:
--
--   1. **(upper bound)** some quantum algorithm making at most $C\tau$ phase queries $O_f|x,c,z\rangle=\omega_q^{cf(x)}|x,c,z\rangle$ outputs, with probability at least $2/3$ on every function $f:[kn]\to\mathbb Z_q$ of exact type $(k^n)$, $\ell$ groups of $r$ distinct inputs with a common value in each group and different values in different groups;
--   2. **(lower bound)** every quantum algorithm with this guarantee makes at least $c\tau$ queries.
--
--   So the worst-case quantum query complexity of finding $r$-collisions in $\ell$ distinct equality classes of a function of exact type $(k^n)$ is $\Theta_{k,r}(\tau)$, with constants independent of $q$. For $r=2$ this is $\Theta_k(\ell^{2/3}N^{1/3})$; for $\ell=1$ it is $\Theta_{k,r}(N^{(2^{r-1}-1)/(2^r-1)})$.
--
--   **Formalization Note** Algorithms are `QAlgorithms.QueryAlg` (start state and unitaries independent of $f$, any finite workspace) with the phase oracle `SelectiveDPT.phaseOracle`, a computational-basis measurement and an output map to $\ell$ groups of $r$ inputs of `Fin N`.
--
--   Differences from the source:
--   - reading: $\Theta_{k,r}(\tau)$ for sufficiently large $N$, measured in the worst case with success probability at least $2/3$ on every function of the type, implicit constants independent of $q$ → $\exists c,C>0,\ \exists N_0$ (depending on $k,r$) chosen before $n,q,\ell$; then an algorithm with $T\le C\tau$ queries succeeding with probability $\ge2/3$ on every $f$, and $T\ge c\tau$ for every algorithm with that guarantee; reason: the standard meaning of $\Theta$ for the worst-case query complexity, uniform over $q$ and the range of $\ell$
--   - encoding: the algorithm models (start state and unitaries independent of the oracle, measurement of the output register) → `QAlgorithms.QueryAlg` with the phase oracle and an output map to $\ell$ groups of $r$ inputs; reason: same class of algorithms
--   - encoding: $[N]$, $\mathbb Z_q$ → `Fin N` (0-based), `ZMod q` with `[NeZero q]`; reason: Lean convention; same instances ($q\ge n\ge1$ once $N_0\ge1$)
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_MultiCollQ_HasExactType
import Definitions.Def_MultiCollQ_collisionRel

namespace MultiCollQ

open QAlgorithms

/-- Theorem 1.1 (Tight collision bounds for pure types) (Peng, Hou, Dong, *Quantum multi-collision
lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), p.3). Fix constants `k ≥ r ≥ 2`
and let `N = kn`. For sufficiently large `N`, every alphabet size `q ≥ n` and every integer
`1 ≤ ℓ ≤ N^{2^{−r}}`, the worst-case quantum query complexity (success probability at least `2/3`
on every function of the prescribed type) of finding `r`-collisions in `ℓ` distinct equality
classes of a function of exact type `(k^n)` is `Θ_{k,r}(τ)`,
`τ = ℓ^{2^{r−1}/(2^r−1)} N^{(2^{r−1}−1)/(2^r−1)}`, with implicit constants independent of `q`.

**Formalization Note.** `Θ_{k,r}` is pinned as: `c, C > 0` and `N₀` depending only on `k, r`, chosen
before `n, q, ℓ`; then (upper) some algorithm with `T ≤ C·τ` queries succeeds with probability
`≥ 2/3` on every `f` of exact type `(k^n)`, and (lower) every algorithm with that guarantee has
`T ≥ c·τ`. Algorithms are `QAlgorithms.QueryAlg` with any finite workspace `Fin wb`, the phase oracle
`O_f|x, c⟩ = ω_q^{c f(x)}|x, c⟩` (2.1), a computational-basis measurement and an output map to `ℓ`
groups of `r` inputs of `[N] = Fin N`. `[NeZero q]` excludes only `q = 0`. Real powers; `r − 1` is
natural subtraction with `r ≥ 2`. -/
theorem theorem_1_1_tight_collision_bound (k r : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ (n q : ℕ) [NeZero q] (ℓ : ℕ),
      N₀ ≤ k * n → n ≤ q → 1 ≤ ℓ → (ℓ : ℝ) ≤ ((k * n : ℕ) : ℝ) ^ ((2 : ℝ) ^ (-(r : ℝ))) →
      let τ : ℝ := (ℓ : ℝ) ^ ((2 : ℝ) ^ (r - 1) / ((2 : ℝ) ^ r - 1)) *
        ((k * n : ℕ) : ℝ) ^ (((2 : ℝ) ^ (r - 1) - 1) / ((2 : ℝ) ^ r - 1))
      (∃ (wb T : ℕ) (A : QueryAlg (Fin (k * n)) (ZMod q) (Fin wb) T)
          (out : (Fin (k * n) × ZMod q) × Fin wb → (Fin ℓ → Fin r → Fin (k * n))),
          (T : ℝ) ≤ C * τ ∧
          ∀ f ∈ exactTypeSet (k * n) q k (pureType k n),
            2 / 3 ≤ SelectiveDPT.successProb A out (collisionRel r ℓ) f) ∧
      (∀ (wb T : ℕ) (A : QueryAlg (Fin (k * n)) (ZMod q) (Fin wb) T)
          (out : (Fin (k * n) × ZMod q) × Fin wb → (Fin ℓ → Fin r → Fin (k * n))),
          (∀ f ∈ exactTypeSet (k * n) q k (pureType k n),
            2 / 3 ≤ SelectiveDPT.successProb A out (collisionRel r ℓ) f) →
          c * τ ≤ T) := by sorry

end MultiCollQ
