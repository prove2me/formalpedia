-- Prove2me | Theorems.Thm_NearEnemy_eval_innerPoly_rows
-- name    : NearEnemy.eval_innerPoly_rows
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:54:40.607243+00:00
-- url     : https://prove2.me/theorems/2e8f1d6d-8461-41e1-8380-3af27109a51a
-- title:
--   Row-matrix evaluation of $\operatorname{innerPoly}$
-- statement:
--   Let $p, q$ be vectors in `EuclideanSpace ℝ ι` (the two rows of a projection matrix), let $k : \operatorname{Fin} 2$ select a row, and let $v$ be a vector in `EuclideanSpace ℝ ι`. Evaluating `innerPoly k v` at the row-matrix $![p, q]$ gives the inner product of the selected row with $v$:
--
--   $$\operatorname{eval}(![p,q],\, \operatorname{innerPoly}(k, v)) = \langle ![p,q](k),\, v\rangle.$$
--
--   This specializes the general evaluation lemma to the concrete two-row matrix form used for planar projections. It is applied whenever a degeneracy condition (e.g. a vanishing minor or inner product) must be read off as the zero set of an explicit nonzero polynomial in the projection entries.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L992-L996

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.eval_innerPoly_rows (p q : EuclideanSpace ℝ ι) (k : Fin 2)
    (v : EuclideanSpace ℝ ι) :
    eval (fun ki ↦ ![p, q] ki.1 ki.2) (innerPoly k v) = ⟪![p, q] k, v⟫ := by sorry
