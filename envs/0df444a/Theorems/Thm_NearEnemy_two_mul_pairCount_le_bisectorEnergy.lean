-- Prove2me | Theorems.Thm_NearEnemy_two_mul_pairCount_le_bisectorEnergy
-- name    : NearEnemy.two_mul_pairCount_le_bisectorEnergy
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:41.396528+00:00
-- url     : https://prove2.me/theorems/8e9e6a0e-e00e-44cf-a21b-3ca026e1a8cc
-- title:
--   Universal floor $2n(n-1) \le$ bisector energy
-- statement:
--   Let $P$ be any finite set of points in the Euclidean plane (`EuclideanSpace ℝ (Fin 2)`), with $n = |P|$. Then the bisector energy, which counts isosceles triples (ordered pairs sharing a perpendicular bisector, including the forced diagonal contributions), is bounded below by twice the ordered-pair count:
--
--   $$2\,|P|\,(|P|-1) \le \operatorname{bisectorEnergy}(P).$$
--
--   This is the foundational lower bound of the Near Enemy project: every planar configuration carries at least this much bisector energy, with equality exactly in the bisector-injective (generic) case. All minimality claims in the bundle theorems are measured against this floor.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L838-L858

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.two_mul_pairCount_le_bisectorEnergy (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * P.card * (P.card - 1) ≤ bisectorEnergy P := by sorry
