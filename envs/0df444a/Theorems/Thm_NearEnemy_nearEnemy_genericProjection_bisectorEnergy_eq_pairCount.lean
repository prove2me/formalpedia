-- Prove2me | Theorems.Thm_NearEnemy_nearEnemy_genericProjection_bisectorEnergy_eq_pairCount
-- name    : NearEnemy.nearEnemy_genericProjection_bisectorEnergy_eq_pairCount
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:02.696142+00:00
-- url     : https://prove2.me/theorems/5e455e85-a41b-4dcc-8e9f-91da2aeecab1
-- title:
--   Generic projections attain bisector energy $2n(n-1)$
-- statement:
--   Let $G$ be a finite set in `EuclideanSpace ℝ ι` and $T$ a real-linear projection to the plane with `ProjectionGeneric T G`. Then the bisector energy of the projected image equals twice the ordered-pair count:
--
--   $$\operatorname{bisectorEnergy}(T(G)) = 2\,|G|\,(|G|-1).$$
--
--   Genericity forces the projected bisectors to be pairwise distinct, so the energy collapses to its absolute floor (via the equality characterization under bisector injectivity), with $|T(G)| = |G|$ by generic injectivity. This is the upper-bound half of the Near Enemy theorem: some planar configuration of $|G|$ points, namely a generic projection, achieves the minimal possible energy.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L924-L933

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.nearEnemy_genericProjection_bisectorEnergy_eq_pairCount {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)} {G : Finset (EuclideanSpace ℝ ι)} (hT : ProjectionGeneric T G) :
    bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) := by sorry
