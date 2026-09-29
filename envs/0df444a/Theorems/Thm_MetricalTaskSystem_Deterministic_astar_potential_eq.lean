-- Prove2me | Theorems.Thm_MetricalTaskSystem_Deterministic_astar_potential_eq
-- name    : MetricalTaskSystem.Deterministic.astar_potential_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:14:29.187989+00:00
-- url     : https://prove2.me/theorems/56ac8f86-cc2c-4ead-b1d5-5e2630f66a11
-- title:
--   Lemma 6.4 — $2\sum_{s\ne s_k}f_k(s)+f_k(s_k)=C_{k-1}+\sum_{i=1}^k d(s_i,s_{i-1})$
-- statement:
--   Let $(S,d)$ be a task system with at least two states and let $s_k$, $f_k$ and $c_k$ be the states, functions and budgets of the algorithm $A^*_d$ started at $s_0$. Put
--   $$F_k=2\sum_{s\neq s_k}f_k(s)+f_k(s_k),\qquad C_{k-1}=\sum_{i=0}^{k-1}c_i .$$
--   Then for every $k\ge0$
--   $$F_k=C_{k-1}+\sum_{i=1}^k d(s_i,s_{i-1}) .$$
--
--   The identity relates the potential $F_k$ to the on-line algorithm's cost, and is one of the three lemmas behind Theorem 6.1.
--
--   **Formalization Note** $C_{k-1}$ is written as $\sum_{i<k}c_i$ to avoid natural-number subtraction; at $k=0$ both sides are $0$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 756, Lemma 6.4 (C_k defined on p. 756)

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 6.4** (Borodin–Linial–Saks 1992, p. 756). Let `F_k = 2 Σ_{x ≠ s_k} f_k(x) + f_k(s_k)`.
Then `F_k = C_{k−1} + Σ_{i=1}^k d(s_i, s_{i−1})`, where `C_{k−1} = Σ_{i=0}^{k−1} c_i`
(for `k = 0` both sides are `0`). -/
theorem astar_potential_eq {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) :
    2 * ∑ x ∈ Finset.univ.erase (s k), fSeq d s k x + fSeq d s k (s k) =
      ∑ i ∈ Finset.range k, cSeq d s i + ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) := by sorry

end MetricalTaskSystem.Deterministic
