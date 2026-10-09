-- Prove2me | Theorems.Thm_KAdaptability_ObjMILP_exact_linearization
-- name    : KAdaptability.ObjMILP.exact_linearization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:59:13.913974+00:00
-- url     : https://prove2.me/theorems/efa64099-c438-41ae-93ff-edbc386bd26e
-- title:
--   Proof of Theorem 2 — exact linearization of z = βy for binary y
-- statement:
--   Let $y\in\{0,1\}^M$ be a binary vector, $\beta\in[0,1]$ a scalar, $z\in\mathbb R^M_+$, and let $e$ be the all-ones vector of $\mathbb R^M$. Then
--   $$z=\beta y\iff z\le y,\quad z\le\beta e,\quad z\ge(\beta-1)e+y.$$
--
--   In the proof of Theorem 2 this replaces the bilinear terms $\beta_ky^k$ of the dual LP by auxiliary variables $z^k$ subject to linear constraints, which yields the MILP (5). The reformulation uses that $0\le\beta\le e$, $y^k\le e$ and that $y^k$ is binary.
--
--   **Formalization Note** The bound $\beta\le1$ is a hypothesis here; in (5) it follows from $\beta\ge0$ and $e^\top\beta=1$. The inequalities are componentwise.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec3 (PDF p. 37), Proof of Theorem 2, linearization of the bilinear terms β_k y^k

import Mathlib

namespace KAdaptability.ObjMILP

/-- Proof of Theorem 2, p. ec3: exact linearization of the bilinear term `β y` for a binary vector
`y ∈ {0,1}^M`, a scalar `0 ≤ β ≤ 1` and `z ∈ ℝ^M_+`:
`z = β y ⟺ z ≤ y, z ≤ β e, z ≥ (β − 1)e + y`, where `e` is the all-ones vector. -/
theorem exact_linearization {M : ℕ} (y z : Fin M → ℝ) (β : ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hz : 0 ≤ z) :
    z = β • y ↔
      (z ≤ y ∧ z ≤ β • (1 : Fin M → ℝ) ∧ (β - 1) • (1 : Fin M → ℝ) + y ≤ z) := by sorry

end KAdaptability.ObjMILP
