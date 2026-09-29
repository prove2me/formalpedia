-- Prove2me | Theorems.Thm_NearEnemy_dist_image_eq_iff_of_sep
-- name    : NearEnemy.dist_image_eq_iff_of_sep
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:54:17.98786+00:00
-- url     : https://prove2.me/theorems/7d6e2216-c2c5-4785-abdc-08ca327a3be0
-- title:
--   Projected distances agree iff differences agree up to sign
-- statement:
--   Let $G$ be a finite point set in `EuclideanSpace ℝ ι`, $T$ a real-linear map to the plane satisfying the separation hypothesis `hsep` (projected distances of unrelated difference vectors stay distinct), and $a,b,c,e \in G$. Then projected distances agree exactly when the source differences agree up to sign:
--
--   $$\operatorname{dist}(Ta,Tb) = \operatorname{dist}(Tc,Te) \iff a - b = c - e \ \lor\ a - b = -(c - e).$$
--
--   This is the distance-transport equivalence: a generic projection preserves the coincidence structure of distances, creating no new equalities and destroying none forced by the sign symmetry. It is the key bridge carrying distance information from the high-dimensional source set to its planar image.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L1679-L1706

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.dist_image_eq_iff_of_sep {G : Finset (EuclideanSpace ℝ ι)}
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hsep : ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
      a - b ≠ c - e → a - b ≠ -(c - e) →
      dist (T a) (T b) ≠ dist (T c) (T e))
    {a b c e : EuclideanSpace ℝ ι}
    (ha : a ∈ G) (hb : b ∈ G) (hc : c ∈ G) (he : e ∈ G) :
    dist (T a) (T b) = dist (T c) (T e) ↔
      (a - b = c - e ∨ a - b = -(c - e)) := by sorry
