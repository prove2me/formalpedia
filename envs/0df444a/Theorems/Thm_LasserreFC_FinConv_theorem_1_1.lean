-- Prove2me | Theorems.Thm_LasserreFC_FinConv_theorem_1_1
-- name    : LasserreFC.FinConv.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:22.761973+00:00
-- url     : https://prove2.me/theorems/efc81667-d552-436f-85f9-1063184672bb
-- title:
--   Theorem 1.1, p. 3 — archimedean + CQ, strict complementarity and SOSC at every global minimizer ⇒ Lasserre's hierarchy has finite convergence
-- statement:
--   Consider problem (1.1) with polynomial data $f, h, g$ and feasible set $K$, and let $f_{\min}$ be its minimum value. Suppose the archimedean condition holds for $h$ and $g$, i.e. $R - \sum_{i=1}^n x_i^2 \in \langle h\rangle_{2t} + Q_t(g)$ for some $t \in \mathbb N$ and $R > 0$. If at every global minimizer $u$ of (1.1) the constraint qualification condition holds and there are Lagrange multipliers satisfying (1.3), (1.4), strict complementarity (1.5) and second order sufficiency (1.7), then Lasserre's hierarchy (1.2) has finite convergence:
--
--   $$\exists\, k \in \mathbb N: \quad f_k = f_{\min}.$$
--
--   Under the archimedean condition, Lasserre's hierarchy was known to converge only asymptotically ($f_k \to f_{\min}$). This theorem identifies the classical optimality conditions of nonlinear programming as a sufficient condition for exact convergence at a finite order.
--
--   **Formalization Note** $f_k$ is the supremum of (1.2) in `EReal`. The minimum value is given as a real number $f_{\min}$ that is the least value of $f$ on $K$ (the page's "let $f_{\min}$ denote the minimum value of (1.1)"); this excludes only $K = \emptyset$, where $f_{\min}$ does not exist. The optimality conditions are required at every global minimizer, with the multipliers of (1.5) and (1.7) those of (1.3)–(1.4).
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 3, Theorem 1.1

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy

namespace LasserreFC.FinConv

open MvPolynomial

/-- Theorem 1.1, p. 3: under the archimedean condition, if CQC, SCC and SOSC hold at every global
minimizer of (1.1), then Lasserre's hierarchy (1.2) has finite convergence: `f_k = f_min` for some `k`. -/
theorem theorem_1_1 {n m1 m2 : ℕ} (P : POP n m1 m2) (harch : IsArchimedean P)
    (fmin : ℝ) (hfmin : IsLeast ((fun x => eval x P.f) '' P.K) fmin)
    (hopt : ∀ u ∈ P.K, IsMinOn (fun x => eval x P.f) P.K u → OptCond P u) :
    ∃ k : ℕ, lasserreValue P k = (fmin : EReal) := by sorry

end LasserreFC.FinConv
