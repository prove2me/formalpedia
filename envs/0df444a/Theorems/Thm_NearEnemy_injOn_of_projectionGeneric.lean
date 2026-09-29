-- Prove2me | Theorems.Thm_NearEnemy_injOn_of_projectionGeneric
-- name    : NearEnemy.injOn_of_projectionGeneric
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:54:55.357374+00:00
-- url     : https://prove2.me/theorems/47408e8d-7acd-404d-860d-3de52a7820cb
-- title:
--   $\operatorname{ProjectionGeneric}$ projections are injective on $G$
-- statement:
--   Let $T$ be a real-linear map from `EuclideanSpace ℝ ι` to the plane (`EuclideanSpace ℝ (Fin 2)`) that is `ProjectionGeneric T G` for a finite set $G$ (i.e. $T$ avoids all finitely many degeneracy polynomials: no collapsed pairs, no new collinearities, no new cosphericalities, separated distances). Then $T$ is injective on $G$:
--
--   $$\operatorname{Set.InjOn}(T,\, G).$$
--
--   Injectivity on the source set is the most basic consequence of genericity: distinct source points must remain distinct after projection, and is invoked every time cardinalities of images are identified with cardinalities of $G$ (e.g. in the energy computation $2|G|(|G|-1)$).
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L899-L904

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.injOn_of_projectionGeneric {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)} {G : Finset (EuclideanSpace ℝ ι)} (hT : ProjectionGeneric T G) :
    Set.InjOn (fun x ↦ T x) ↑G := by sorry
