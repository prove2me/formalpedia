-- Prove2me | Theorems.Thm_NearEnemy_sharedBisector_parallel_and_sum_orth
-- name    : NearEnemy.sharedBisector_parallel_and_sum_orth
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:33.549489+00:00
-- url     : https://prove2.me/theorems/f7b2e956-584f-4f33-afa7-00210462c715
-- title:
--   A shared bisector forces parallel directions and midpoint orthogonality
-- statement:
--   Let $p,q,p',q'$ be points in the plane with equal perpendicular bisectors, $\operatorname{perpBisector}(p,q) = \operatorname{perpBisector}(p',q')$. Then the chords are parallel and the midpoint displacement is orthogonal to the chord direction:
--
--   $$(\exists\, t : \mathbb{R},\ q' - p' = t \cdot (q - p))\ \land\ \langle p + q - (p' + q'),\, q - p\rangle = 0.$$
--
--   This is the geometric analysis of a bisector coincidence: sharing a bisector constrains the two segments to be parallel with midpoints displaced along the bisector. Combined with the midpoint-identification lemma, it drives the proof that generic (general-position) configurations have injective bisectors, hence minimal energy.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L655-L714

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.sharedBisector_parallel_and_sum_orth {p q p' q' : EuclideanSpace ℝ (Fin 2)}
    (h : perpBisector p q = perpBisector p' q') :
    (∃ t : ℝ, q' - p' = t • (q - p)) ∧ ⟪p + q - (p' + q'), q - p⟫ = 0 := by sorry
