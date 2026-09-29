-- Prove2me | Theorems.Thm_NearEnemy_bisectorEnergy_eq_of_bisectorInjective
-- name    : NearEnemy.bisectorEnergy_eq_of_bisectorInjective
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:18.110244+00:00
-- url     : https://prove2.me/theorems/27ffd662-b0bf-4f15-ac4c-60a8664e0df4
-- title:
--   Bisector energy equals $2n(n-1)$ under bisector injectivity
-- statement:
--   Let $P$ be a finite set of points in the Euclidean plane (modelled as `EuclideanSpace ℝ (Fin 2)`), and assume `BisectorInjectiveOnPairs P`, i.e. distinct unordered pairs of points of $P$ have distinct perpendicular bisectors. Then the bisector energy attains its absolute floor:
--
--   $$\operatorname{bisectorEnergy}(P) = 2\,|P|\,(|P|-1).$$
--
--   This is the equality characterization companion to the universal lower bound: under bisector injectivity there are no coincidences beyond the forced ones, so the energy is exactly the count of ordered pairs times two. In the project it certifies that generic projections (which force bisector injectivity) produce energy-minimal configurations.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L860-L885

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.bisectorEnergy_eq_of_bisectorInjective {P : Finset (EuclideanSpace ℝ (Fin 2))}
    (hP : BisectorInjectiveOnPairs P) :
    bisectorEnergy P = 2 * P.card * (P.card - 1) := by sorry
