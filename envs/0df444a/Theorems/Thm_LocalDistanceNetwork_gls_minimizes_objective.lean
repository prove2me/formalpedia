-- Prove2me | Theorems.Thm_LocalDistanceNetwork_gls_minimizes_objective
-- name    : LocalDistanceNetwork.gls_minimizes_objective
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:23:40.681978+00:00
-- url     : https://prove2.me/theorems/cd4579ba-e19c-4b78-ab7d-751db3c5ef97
-- title:
--   Eq. (B.2) — the GLS estimate minimizes the weighted quadratic form $Q$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank (the map $X\mapsto AX$ is injective), let $W\in\mathbb R^{m\times m}$ be symmetric positive definite, and let $Y\in\mathbb R^{m}$. Then the generalized least-squares estimate
--   $$
--   \hat X_W=(A^{\mathsf T}WA)^{-1}A^{\mathsf T}W\,Y
--   $$
--   minimizes the quadratic form $Q(X)=(Y-AX)^{\mathsf T}W(Y-AX)$ of Eq. (B.2): for every $X\in\mathbb R^{n}$,
--   $$
--   Q(\hat X_W)\le Q(X).
--   $$
--
--   This identifies the closed-form estimator with the solution of the minimization problem that the Distance Network solves, both for a general weight matrix and for $W=C^{-1}$, where $Q$ is the $\chi^2$ of Eq. (B.1).
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix

namespace LocalDistanceNetwork
theorem gls_minimizes_objective {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (W : Matrix m m ℝ) (hW : W.PosDef) (Y : m → ℝ) (X : n → ℝ) :
    glsObjective A W Y (glsEstimate A W Y) ≤ glsObjective A W Y X := by sorry
end LocalDistanceNetwork
