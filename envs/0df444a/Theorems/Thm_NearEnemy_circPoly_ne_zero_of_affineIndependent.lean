-- Prove2me | Theorems.Thm_NearEnemy_circPoly_ne_zero_of_affineIndependent
-- name    : NearEnemy.circPoly_ne_zero_of_affineIndependent
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:54:03.745072+00:00
-- url     : https://prove2.me/theorems/65c327d8-986e-4fd1-b0be-33a928dbcd3f
-- title:
--   $\operatorname{circPoly}$ is nonzero on affinely independent quadruples
-- statement:
--   Let $a,b,c,e$ be points in `EuclideanSpace ℝ ι` that are affinely independent (the hypothesis `hind : AffineIndependent ℝ ![a,b,c,e]`). Then the circumsphere-detecting polynomial is nonzero on this quadruple:
--
--   $$\operatorname{circPoly}(a,b,c,e) \neq 0.$$
--
--   Affine independence of the four points — full $3$-dimensional span of the difference vectors — is enough to keep `circPoly` from vanishing. Only this direction is proved here; the converse, that vanishing of `circPoly` forces a cospherical or degenerate quadruple, is not part of this development. Note that affine independence of four points requires ambient dimension at least $3$, so in the plane the hypothesis has no instances. This is the highest-codimension nonvanishing input to the polynomial method that builds a generic projection avoiding cospherical quadruples; the coplanar and no-three-collinear cases are handled by their own lemmas.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L1170-L1240

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.circPoly_ne_zero_of_affineIndependent {a b c e : EuclideanSpace ℝ ι}
    (hind : AffineIndependent ℝ ![a, b, c, e]) :
    circPoly a b c e ≠ 0 := by sorry
