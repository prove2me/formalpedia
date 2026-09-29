-- Prove2me | Theorems.Thm_NearEnemy_exists_smul_eq_of_forall_inner_det_eq_zero
-- name    : NearEnemy.exists_smul_eq_of_forall_inner_det_eq_zero
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:54:47.814674+00:00
-- url     : https://prove2.me/theorems/471295b9-d30d-4508-94cf-55fc7e5f3532
-- title:
--   Vanishing inner-product determinants force collinearity
-- statement:
--   Let $V$ be a real inner-product space and $v, w \in V$ such that every $2 \times 2$ determinant of inner products against arbitrary test vectors $p, q$ vanishes:
--
--   $$\forall\, p\, q \in V,\quad \langle p, v\rangle\langle q, w\rangle - \langle p, w\rangle\langle q, v\rangle = 0.$$
--
--   Then $v$ and $w$ are linearly dependent over $\mathbb{R}$:
--
--   $$(\exists\, t : \mathbb{R},\ w = t \cdot v)\ \lor\ (\exists\, t : \mathbb{R},\ v = t \cdot w).$$
--
--   In words, the Gram-type rank-one condition forces one vector to be a scalar multiple of the other. This lemma converts analytic degeneracy hypotheses (vanishing determinants) into the geometric conclusion of parallelism, used when a shared bisector forces direction vectors to align.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L275-L305

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.exists_smul_eq_of_forall_inner_det_eq_zero {v w : V}
    (h : ∀ p q : V, ⟪p, v⟫ * ⟪q, w⟫ - ⟪p, w⟫ * ⟪q, v⟫ = 0) :
    (∃ t : ℝ, w = t • v) ∨ (∃ t : ℝ, v = t • w) := by sorry
