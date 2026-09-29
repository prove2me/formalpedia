-- Prove2me | Theorems.Thm_LinearOptimization_network_flow_decomposition_including_zero
-- name    : LinearOptimization.network_flow_decomposition_including_zero
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-06T18:23:37.633575+00:00
-- url     : https://prove2.me/theorems/e3dcc6d5-acec-43de-af4e-99a0e3b349c7
-- title:
--   Flow decomposition including the zero circulation
-- statement:
--   Let $G=(\mathcal N,\mathcal A)$ be a finite directed network with no self-loops, and let $f\in\mathbb R^{\mathcal A}$ be a nonnegative circulation, so $Af=0$. Then there are simple directed cycles $C_1,\ldots,C_k$ and positive real coefficients $a_1,\ldots,a_k$ such that
--
--   $$
--   f=\sum_{i=1}^k a_i h^{C_i}.
--   $$
--
--   If every coordinate of $f$ is integral, the coefficients may all be chosen as positive integers. The statement includes the zero circulation: in that case $k=0$ and the displayed sum is empty.
--
--   This closed form is a reusable strengthening of the printed nonzero flow-decomposition lemma and removes a routine boundary-case hypothesis from downstream applications.
--
--   **Formalization Note** Each $C_i$ is represented by a simple forward-only cycle step list, and $h^{C_i}$ is its traversal vector.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Lemma 7.1 and its proof, p. 298 (the proof explicitly notes that the zero case is trivial with k = 0)

import Definitions.Def_LinearOptimization_NetworkFlowProblem

open Matrix

theorem LinearOptimization.network_flow_decomposition_including_zero {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (hloop : HasNoSelfLoops arcs)
    (f : Fin m → ℝ) (hnn : 0 ≤ f) (hcirc : IsCirculation arcs f) :
    (∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℝ),
      (∀ i, ∃ v, IsCycle arcs v (cyc i)) ∧
      (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
      (∀ i, 0 < a i) ∧
      f = fun e => ∑ i, a i * traversalVector (cyc i) e) ∧
    ((∀ e, ∃ z : ℤ, f e = (z : ℝ)) →
      ∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℤ),
        (∀ i, ∃ v, IsCycle arcs v (cyc i)) ∧
        (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
        (∀ i, 0 < a i) ∧
        f = fun e => ∑ i, (a i : ℝ) * traversalVector (cyc i) e) := by
  sorry
