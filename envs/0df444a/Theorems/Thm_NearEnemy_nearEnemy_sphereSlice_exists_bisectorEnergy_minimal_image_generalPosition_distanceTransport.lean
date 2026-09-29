-- Prove2me | Theorems.Thm_NearEnemy_nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
-- name    : NearEnemy.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:26.283267+00:00
-- url     : https://prove2.me/theorems/095fe908-699c-48d2-8287-e5a3147f2d39
-- title:
--   Spherical sets project to minimal-energy general-position images
-- statement:
--   Let $G$ be a finite set in `EuclideanSpace ℝ ι` contained in a metric sphere of center $\mathrm{center}$ and radius $R$ (hypothesis `hG`: every $x \in G$ lies in `Metric.sphere center R`). Then there exists a real-linear map $T$ to the plane delivering the same full bundle as in the no-three-collinear case: injectivity on $G$, $\operatorname{bisectorEnergy}(T(G)) = 2|G|(|G|-1)$ with minimality among equal-cardinality planar sets, general position of the image (no three collinear, no four cospherical), $\operatorname{rotationEnergy}(T(G)) = 0$, exact distance transport, and the distance-class counting identity:
--
--   $$\exists\, T,\quad \operatorname{bisectorEnergy}(T(G)) = 2\,|G|\,(|G|-1)\ \land\ \operatorname{rotationEnergy}(T(G)) = 0\ \land\ \text{(general position + distance transport)}.$$
--
--   This is the spherical-source counterpart of the main bundle. Sphere membership is the only hypothesis: no general-position assumption is imposed on $G$, because a line meets a sphere in at most two points, so a set on a sphere is automatically no-three-collinear. Every four points of $G$ are of course cospherical; it is the planar image that is shown free of cospherical quadruples. The corollary therefore extends the Near Enemy conclusion to spherical configurations at no extra cost in hypotheses.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L3379-L3413

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport {center : EuclideanSpace ℝ ι} {R : ℝ} {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ x ∈ G, x ∈ Metric.sphere center R) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) ∧
      (∀ P' : Finset (EuclideanSpace ℝ (Fin 2)), P'.card = G.card →
        bisectorEnergy (G.image fun x ↦ T x) ≤ bisectorEnergy P') ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
          ¬ Collinear ℝ ({q₁, q₂, q₃} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), ∀ q₄ ∈ G.image (fun x ↦ T x),
        q₁ ≠ q₂ → q₁ ≠ q₃ → q₁ ≠ q₄ → q₂ ≠ q₃ → q₂ ≠ q₄ → q₃ ≠ q₄ →
          ¬ EuclideanGeometry.Cospherical
            ({q₁, q₂, q₃, q₄} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      rotationEnergy (G.image fun x ↦ T x) = 0 ∧
      (∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
        (dist (T a) (T b) = dist (T c) (T e) ↔
          (a - b = c - e ∨ a - b = -(c - e)))) ∧
      (((G.image fun x ↦ T x).offDiag).image fun q ↦ dist q.1 q.2).card =
        ((G.offDiag).image fun p ↦
          ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι))).card := by sorry
