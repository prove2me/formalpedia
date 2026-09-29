-- Prove2me | Theorems.Thm_NearEnemy_rowMap_apply
-- name    : NearEnemy.rowMap_apply
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:35.050658+00:00
-- url     : https://prove2.me/theorems/8eb1f714-e1f9-4771-9159-7b0cce1fccf4
-- title:
--   $\operatorname{rowMap}$ evaluates as an inner product
-- statement:
--   Let $r : \operatorname{Fin} 2 \to \operatorname{EuclideanSpace} \mathbb{R}\ \iota$ be a two-row matrix of vectors and $x$ a vector in `EuclideanSpace ℝ ι`. Then applying the row map at row $k$ is the inner product with that row:
--
--   $$\operatorname{rowMap}(r,\, x,\, k) = \langle r(k),\, x\rangle.$$
--
--   This `simp` lemma fixes the semantics of the projection-as-matrix construction: a linear map to the plane presented by rows $r$ acts by inner products against those rows. It is used pervasively to unfold `rowMap`/`rowOf` expressions into inner products that the polynomial evaluation lemmas (`eval_innerPoly`) can then recognize.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L982-L984

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

@[simp]
theorem NearEnemy.rowMap_apply (r : Fin 2 → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (k : Fin 2) :
    rowMap r x k = ⟪r k, x⟫ := by sorry
