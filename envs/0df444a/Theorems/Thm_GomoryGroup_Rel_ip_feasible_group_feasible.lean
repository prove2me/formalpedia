-- Prove2me | Theorems.Thm_GomoryGroup_Rel_ip_feasible_group_feasible
-- name    : GomoryGroup.Rel.ip_feasible_group_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:29:38.950987+00:00
-- url     : https://prove2.me/theorems/7fa21f83-91a9-424d-9884-d41b39af84ca
-- title:
--   proof of THEOREM 1, p. 263 — applying f to (5): the x_N part of a feasible solution of P2 is feasible for (4)
-- statement:
--   Let $B$ be an integer $m\times m$ matrix, $N$ an integer $m\times n$ matrix and $b\in\mathbb Z^m$. If $x_B\in\mathbb N^m$ and $x_N\in\mathbb N^n$ satisfy
--   $$Bx_B+Nx_N=b,$$
--   i.e. $(x_B,x_N)$ is feasible for P2, then $x_N$ is feasible for the group problem (4):
--   $$\sum_{i=m+1}^{m+n}\bar\alpha_ix_i=\bar b\ \text{ in } M(I)/M(B),\qquad\text{i.e.}\qquad b-Nx_N\in\mathfrak L_B.$$
--
--   Applying the quotient homomorphism $f$ makes the basic columns disappear; this is how every solution of P2 projects to a solution of (4).
--
--   **Formalization Note** Feasibility for (4) is $b-Nx_N=Bk$ for some $k\in\mathbb Z^m$. No standing hypothesis is needed, so none is assumed.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 263, after (6)

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem ip_feasible_group_feasible {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    ∀ (xB : Fin m → ℕ) (xN : Fin n → ℕ),
      IsIPFeasible B N b xB xN → IsGroupFeasible B N b xN := by sorry

end GomoryGroup.Rel
