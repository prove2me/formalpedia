-- Prove2me | Theorems.Thm_NearEnemy_innerPoly_ne_zero
-- name    : NearEnemy.innerPoly_ne_zero
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:09.06019+00:00
-- url     : https://prove2.me/theorems/9cecf37a-31b5-4218-ace9-43116e0cb97b
-- title:
--   $\operatorname{innerPoly}$ of a nonzero difference is nonzero
-- statement:
--   Let $a, b$ be points in `EuclideanSpace ℝ ι` with $a \neq b$. Then the linear polynomial built from their difference at row index $0$ is a nonzero polynomial:
--
--   $$\operatorname{innerPoly}(0,\, a - b) \neq 0.$$
--
--   Since $a - b \neq 0$, at least one coordinate functional against it is nontrivial, so the associated formal polynomial cannot be identically zero. This is the atomic nonvanishing fact seeding the polynomial method: every pair of distinct source points contributes a genuine (avoidable) degeneracy condition $\langle r_0, a-b\rangle = 0$ cutting out the bad projections.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L1022-L1028

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.innerPoly_ne_zero {a b : EuclideanSpace ℝ ι} (hab : a ≠ b) :
    innerPoly (ι := ι) 0 (a - b) ≠ 0 := by sorry
