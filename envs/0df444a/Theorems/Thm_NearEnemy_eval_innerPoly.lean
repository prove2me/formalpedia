-- Prove2me | Theorems.Thm_NearEnemy_eval_innerPoly
-- name    : NearEnemy.eval_innerPoly
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:54:32.988335+00:00
-- url     : https://prove2.me/theorems/43c6b350-5bbd-4ae5-ae97-abc5d6ad3dc9
-- title:
--   Evaluation of $\operatorname{innerPoly}$ is an inner product with a row
-- statement:
--   Let $f : \operatorname{Fin} 2 \times \iota \to \mathbb{R}$ be a coefficient matrix (two rows indexed by $k : \operatorname{Fin} 2$), and let $v$ be a vector in `EuclideanSpace ℝ ι`. Then evaluating the polynomial `innerPoly k v` at $f$ recovers the inner product of the $k$-th row of $f$ with $v$:
--
--   $$\operatorname{eval}(f,\, \operatorname{innerPoly}(k, v)) = \langle \operatorname{rowOf}(f, k),\, v\rangle.$$
--
--   This evaluation identity is the semantic core of the polynomial encoding: the formal polynomial `innerPoly` faithfully represents the linear functional $x \mapsto \langle r_k, x\rangle$ determined by a projection row. It lets the nonvanishing results proved for polynomials transfer to geometric statements about inner products with projection rows.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L986-L990

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.eval_innerPoly (f : Fin 2 × ι → ℝ) (k : Fin 2)
    (v : EuclideanSpace ℝ ι) :
    eval f (innerPoly k v) = ⟪rowOf f k, v⟫ := by sorry
