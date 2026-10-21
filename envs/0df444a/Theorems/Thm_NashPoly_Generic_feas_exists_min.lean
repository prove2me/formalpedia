-- Prove2me | Theorems.Thm_NashPoly_Generic_feas_exists_min
-- name    : NashPoly.Generic.feas_exists_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:48.818111+00:00
-- url     : https://prove2.me/theorems/906dc3c6-47f1-4948-b5dd-9373be81c797
-- title:
--   Proof of Theorem 3.2, p. 10 — since Θ is positive definite, (3.10) has a minimizer unless it is infeasible
-- statement:
--   Let a NEPP be given, with any matrix polynomials $H_i$ defining the multiplier expressions $\lambda_{i,j}(x)$ and any cut sets $K_i\subseteq\mathbb R^{n_i}$. Let $\Theta\in\mathbb R^{(n+1)\times(n+1)}$ be symmetric positive definite and $[x]_1=(1,x_1,\dots,x_n)$. If the feasible set $\mathrm{Feas}(K)$ of (3.10) is nonempty, then the problem
--   $$\min_x\ [x]_1^T\,\Theta\,[x]_1\quad\text{s.t.}\quad x\in\mathrm{Feas}(K)$$
--   has a minimizer: there is $u\in\mathrm{Feas}(K)$ with $[u]_1^T\Theta[u]_1\le[x]_1^T\Theta[x]_1$ for all $x\in\mathrm{Feas}(K)$.
--
--   This guarantees that Step 1 of Algorithm 3.1 can always be carried out.
--
--   **Formalization Note** Positive definiteness of a real matrix includes symmetry. No assumption on $H_i$ or $K_i$ is needed.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 10, proof of Theorem 3.2

import Mathlib
import Definitions.Def_NashPoly_Generic_MultiplierExpr

namespace NashPoly.Generic

open MvPolynomial Matrix

/-- Proof of Theorem 3.2, p. 10: since `Θ` is positive definite, (3.10) has a minimizer of
`[x]_1^T Θ [x]_1` unless it is infeasible (for any multiplier expressions and any cut sets). -/
theorem feas_exists_min {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (K : (i : Fin N) → Set (Fin (n i) → ℝ))
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) (hΘ : Θ.PosDef)
    (hne : (P.Feas H K).Nonempty) :
    ∃ u ∈ P.Feas H K, IsMinOn (theta Θ) (P.Feas H K) u := by sorry

end NashPoly.Generic
