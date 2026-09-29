-- Prove2me | Theorems.Thm_NearEnemy_nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair
-- name    : NearEnemy.nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:18.876255+00:00
-- url     : https://prove2.me/theorems/171ec994-46c9-4915-9a20-2d98747cedeb
-- title:
--   In general position, a shared midpoint plus parallelism forces the same pair
-- statement:
--   Let $a,b,c,e$ be points in `EuclideanSpace ℝ ι` satisfying a general-position hypothesis `hgp` (if $a \neq b$, $c \neq a$, $c \neq b$ then $\{a,b,c\}$ is not collinear), the midpoint coincidence $a + b = c + e$, and parallelism $c - e = t \cdot (a - b)$ for some $t : \mathbb{R}$. Then the two pairs coincide as sets:
--
--   $$\{a, b\} = \{c, e\}\quad\text{(as sets)}.$$
--
--   Geometrically: two segments with the same midpoint that are parallel must be the same segment, unless a collinearity degeneracy intervenes, which `hgp` excludes. This rigidity fact is the engine of bisector injectivity: a shared perpendicular bisector forces equal midpoints and parallel directions, and this lemma closes the trap by identifying the pairs.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L464-L523

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair {ι : Type*} [Fintype ι]
    {a b c e : EuclideanSpace ℝ ι}
    (hgp : a ≠ b → c ≠ a → c ≠ b →
      ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)))
    (hmid : a + b = c + e)
    (hpar : ∃ t : ℝ, c - e = t • (a - b)) :
    ({a, b} : Set (EuclideanSpace ℝ ι)) =
      ({c, e} : Set (EuclideanSpace ℝ ι)) := by sorry
