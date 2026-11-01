-- Prove2me | Theorems.Thm_LocalDOvS_SUS_lemma_EC_8
-- name    : LocalDOvS.SUS.lemma_EC_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:29:55.531488+00:00
-- url     : https://prove2.me/theorems/a315d4ed-777c-4f8e-96ed-8e7ab45210c6
-- title:
--   Lemma EC.8, p.ec14 (corrected: $x_L, x_U := y$; $\min S_k - d_k \le x_{L,k}$)
-- statement:
--   Consider the corrected shrinking uniform sampling algorithm with the corrected bounds: $x_{L,1}=1$, $x_{U,1}=N$; after a Type-I Operation on $x,y$, $x_{U,k+1}:=y$ if $x<y$ and $x_{L,k+1}:=y$ if $y<x$; otherwise unchanged. Then for every iteration $k$,
--
--   $$
--   \min S_k-d_k\le x_{L,k}\le\min S_k\qquad\text{and}\qquad \max S_k\le x_{U,k}\le\max S_k+d_k ,
--   $$
--
--   where $d_k$ is the step size. The statement is deterministic: it holds for the iteration in progress after any history, for every rule choosing the Type-I pair and breaking ties.
--
--   The interval $\{x_{L,k},\dots,x_{U,k}\}$ is the set of candidate solutions in the proof of Theorem 2; the lemma says that the active set approximates it up to one step on each side.
--
--   Differences from the source:
--   - correction: x_{U,k+1} := y − d_k and x_{L,k+1} := y + d_k (p.ec14) → x_{U,k+1} := y and x_{L,k+1} := y; reason: the printed bounds exclude integers strictly between grid points: f = (9, 6, 3, 2.5, 3.2, 6, 9), S = {1, 3, 5, 7}, d = 2, x = 3, y = 5 gives x_U = 3 and the minimizer 4 is excluded, so the proof's second event fails
--   - correction: x_{L,k} = min S_k and x_{U,k} ≤ max S_k + d_k → min S_k − d_k ≤ x_{L,k} ≤ min S_k and x_{U,k} ≤ max S_k + d_k; reason: with the corrected bounds x_{L,k} = y = min S_{k+1} − d_k after a second-case Type-I Operation, so the equality becomes the two-sided bound
--   - generalization: (EC.11) only → also max S_k ≤ x_{U,k}; reason: the proof of Theorem 2 uses it (a := M̃ − M ∈ [0, 1], p.ec17) without proving it
--   - generalization: for any iteration k of a run → for the state after any history and every pick and tie rule; reason: contains every run
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Lemma EC.8, p.ec14

import Mathlib
import Definitions.Def_LocalDOvS_SUS_susState__311ba0

open scoped NNReal

namespace LocalDOvS.SUS

/-- **Lemma EC.8, p.ec14** (Zhang–Zheng–Lavaei, arXiv:2012.02427v2), for the corrected bounds
`x_{L,k}`, `x_{U,k}` (see `typeIUpdate`). For every iteration `k` of the corrected shrinking
uniform sampling algorithm,
`min S_k − d_k ≤ x_{L,k} ≤ min S_k` and `max S_k ≤ x_{U,k} ≤ max S_k + d_k`.
The statement is deterministic: it holds for the state reached after any history `h` (in
particular along every run on every tape), for every pick and tie rule.

**Formalization Note.** `min S_k = x0`, `max S_k = x0 + (M − 1)·s`, `d_k = s`; the
inequalities are in `ℤ`, so there is no truncated subtraction. -/
theorem lemma_EC_8 (N : ℕ) (hN : 2 ≤ N) (σ : ℝ≥0) (ε δ : ℝ)
    (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (tie : SUSState → (ℕ → ℕ → ℝ) → Bool)
    (h : List (ℕ × ℝ)) :
    let st := susState N σ ε δ pick tie h
    ((st.x0 : ℤ) - st.s ≤ st.xL ∧ (st.xL : ℤ) ≤ st.x0) ∧
    ((st.x0 : ℤ) + ((st.M : ℤ) - 1) * st.s ≤ st.xU ∧
      (st.xU : ℤ) ≤ st.x0 + ((st.M : ℤ) - 1) * st.s + st.s) := by sorry

end LocalDOvS.SUS
