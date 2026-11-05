-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_isCompact_primalBodyVec
-- name    : ModernConvex.Relaxations.isCompact_primalBodyVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:57:37.446452+00:00
-- url     : https://prove2.me/theorems/28f9029a-f24e-43e1-a159-80e83babd324
-- title:
--   The primal Max-Cut SDP body is compact
-- statement:
--   **The primal body of the Max-Cut semidefinite relaxation is compact.**
--
--   In ellipsoid coordinates, the body is $K=\{x : \texttt{finToMat}\ x\succeq0,\ (\texttt{finToMat}\ x)_{ii}=1\ \forall i\}$.
--
--   *Closed:* the map $x\mapsto\texttt{finToMat}\ x$ is continuous, the positive semidefinite cone is closed, and each diagonal constraint $(\texttt{finToMat}\ x)_{ii}=1$ is the preimage of a point under a continuous linear functional; $K$ is an intersection of closed sets.
--
--   *Bounded:* a positive semidefinite matrix with unit diagonal has $|X_{ij}|\le1$ (its $2\times2$ principal minors are nonnegative), so every coordinate of every point of $K$ has modulus at most one, i.e. $\|x\|_\infty\le1$.
--
--   In the finite-dimensional space $\mathbb R^{n^2}$ (a proper metric space) closed and bounded implies compact by Heine–Borel. This is the `IsConvexBody` compactness hypothesis of the ellipsoid method of Bubeck's Theorem 2.4, and the reason the ellipsoid run on this body terminates with a genuine near-optimal feasible point.
-- source:
--   Heine-Borel plus the $2\times2$ principal minor bound; the compactness hypothesis of Bubeck, arXiv:1405.4980v2, Thm 2.4, p. 250, for the MAXCUT body of Ben-Tal-Nemirovski (4.3.15).

import Mathlib
import Definitions.Def_ModernConvex_MatrixVec
import Definitions.Def_ModernConvex_PrimalBody
import Theorems.Thm_ModernConvex_Relaxations_isClosed_posSemidef
import Theorems.Thm_ModernConvex_Relaxations_abs_entry_le_one

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The primal body of the Max-Cut SDP is compact.** The positive semidefinite cone is closed,
the diagonal constraints are affine, and every entry of a unit-diagonal semidefinite matrix has
modulus at most one — so the body is closed and bounded in `ℝ^{n·n}`, hence compact. -/
theorem isCompact_primalBodyVec (n : ℕ) : IsCompact (primalBodyVec n) := by sorry

end ModernConvex.Relaxations
