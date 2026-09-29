-- Prove2me | Theorems.Thm_NearEnemy_circPoly_ne_zero_of_noThreeCollinear
-- name    : NearEnemy.circPoly_ne_zero_of_noThreeCollinear
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:20.006986+00:00
-- url     : https://prove2.me/theorems/719c9f02-1489-42f5-97db-88405e6f26f6
-- title:
--   $\operatorname{circPoly}$ is nonzero under no-three-collinearity
-- statement:
--   Let $a,b,c,e$ be points in `EuclideanSpace ℝ ι` with $a \neq b$ and $a \neq e$, and assume no-three-collinearity for the triples $\{a,b,c\}$ and $\{b,c,e\}$. Then
--
--   $$\operatorname{circPoly}(a,b,c,e) \neq 0.$$
--
--   This is the base nonvanishing lemma for the cosphericality polynomial under only general-position (no-three-collinear) hypotheses, with no planarity or independence assumed. It guarantees that each forbidden cosphericality condition is a genuine nonzero polynomial constraint, hence avoidable by a generic choice of projection; the coplanar and affinely-independent variants refine it for the dimension stratification.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L1532-L1602

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.circPoly_ne_zero_of_noThreeCollinear {a b c e : EuclideanSpace ℝ ι}
    (hab : a ≠ b) (hae : a ≠ e)
    (habc : ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)))
    (hbce : ¬ Collinear ℝ ({b, c, e} : Set (EuclideanSpace ℝ ι))) :
    circPoly a b c e ≠ 0 := by sorry
