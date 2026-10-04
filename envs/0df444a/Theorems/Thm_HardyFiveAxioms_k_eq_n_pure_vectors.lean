-- Prove2me | Theorems.Thm_HardyFiveAxioms_k_eq_n_pure_vectors
-- name    : HardyFiveAxioms.k_eq_n_pure_vectors
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T17:14:20.278986+00:00
-- url     : https://prove2.me/theorems/3f6f089e-98f2-4f97-af7a-f1e19787018e
-- title:
--   Case $K=N$: the solutions of $\sum_k(p^k)^2=1$, $0\le p^k\le1$, $\sum_kp^k=1$ are basis vectors
-- statement:
--   Let $p=(p^1,\dots,p^N)\in\mathbb R^N$ satisfy
--
--   $$\sum_{k=1}^N(p^k)^2=1,\qquad 0\le p^k\le1\ \ (k=1,\dots,N),\qquad \sum_{k=1}^Np^k=1 .$$
--
--   Then one entry of $p$ equals $1$ and all others equal $0$, i.e. $p=e_n$ for some $n$.
--
--   In the case $K=N$, Hardy shows that $D$ is the identity, so pure states satisfy Eq. (71), Eqs. (72)–(73) hold for normalized states, and the pure states are only the basis vectors. This is the step used to rule out $K=N$ by the continuity axiom.
--
--   **Formalization Note** Entries are indexed by `Fin N`.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 19–20, Section 8.5, Eqs. (70)–(73)

import Mathlib

namespace HardyFiveAxioms

/-- Hardy 2001, Section 8.5, Eqs. (71)–(73): the only solutions of `∑ₖ (pᵏ)² = 1`,
`0 ≤ pᵏ ≤ 1`, `∑ₖ pᵏ = 1` are the basis vectors (one entry `1`, all others `0`). -/
theorem k_eq_n_pure_vectors (N : ℕ) (p : Fin N → ℝ)
    (hsq : ∑ k, p k ^ 2 = 1) (hbd : ∀ k, 0 ≤ p k ∧ p k ≤ 1) (hnorm : ∑ k, p k = 1) :
    ∃ n : Fin N, p = Pi.single n 1 := by sorry

end HardyFiveAxioms
