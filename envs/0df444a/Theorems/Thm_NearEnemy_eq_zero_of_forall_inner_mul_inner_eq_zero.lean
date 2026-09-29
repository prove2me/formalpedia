-- Prove2me | Theorems.Thm_NearEnemy_eq_zero_of_forall_inner_mul_inner_eq_zero
-- name    : NearEnemy.eq_zero_of_forall_inner_mul_inner_eq_zero
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:54:25.710596+00:00
-- url     : https://prove2.me/theorems/1e057eae-e466-4bc7-9cb1-4a84f6d8aafc
-- title:
--   For nonzero $v$, vanishing of $\langle r,m\rangle\langle r,v\rangle$ for all $r$ forces $m = 0$
-- statement:
--   Let $V$ be a real inner-product space, $v \in V$ a nonzero vector, and $m \in V$ such that the product of inner products vanishes against every test vector $r$:
--
--   $$\forall\, r \in V,\quad \langle r, m\rangle\, \langle r, v\rangle = 0 \quad\Longrightarrow\quad m = 0.$$
--
--   Since $v \neq 0$, testing at $r = m$ (or decomposing along $v$) forces $m$ to vanish. This elementary linear-algebra vanishing lemma is a workhorse in the analysis of the degeneracy loci of the projection polynomials: it converts a universally-quantified product condition into the conclusion that a coefficient vector is zero.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L241-L259

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.eq_zero_of_forall_inner_mul_inner_eq_zero {m v : V} (hv : v ≠ 0)
    (h : ∀ r : V, ⟪r, m⟫ * ⟪r, v⟫ = 0) : m = 0 := by sorry
