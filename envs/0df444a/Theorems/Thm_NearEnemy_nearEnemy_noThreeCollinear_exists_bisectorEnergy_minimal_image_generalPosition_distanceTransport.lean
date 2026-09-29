-- Prove2me | Theorems.Thm_NearEnemy_nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
-- name    : NearEnemy.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:22.07616+00:00
-- url     : https://prove2.me/theorems/10ea9d8a-69c7-4dd4-92bd-30c77265a763
-- title:
--   No-three-collinear sets project to minimal-energy general-position images
-- statement:
--   Let $G$ be a finite set in `EuclideanSpace ℝ ι` with no three collinear (hypothesis `hG`: any three distinct points of $G$ are not `Collinear`). Then there exists a real-linear map $T$ to the plane such that, writing $Q = T(G)$: (i) $T$ is injective on $G$; (ii) $\operatorname{bisectorEnergy}(Q) = 2|G|(|G|-1)$ and $Q$ minimizes bisector energy among all planar sets of the same cardinality; (iii) $Q$ is in general position (no three collinear, no four cospherical); (iv) $\operatorname{rotationEnergy}(Q) = 0$; (v) distances transport exactly, $\operatorname{dist}(Ta,Tb) = \operatorname{dist}(Tc,Te) \iff a-b = \pm(c-e)$; (vi) the projected distance count matches the source sign-paired difference-class count:
--
--   $$\exists\, T,\quad \operatorname{bisectorEnergy}(T(G)) = 2\,|G|\,(|G|-1)\ \land\ \operatorname{rotationEnergy}(T(G)) = 0\ \land\ \text{(general position + distance transport)}.$$
--
--   This is the flagship single-witness bundle for no-three-collinear sources: one projection simultaneously achieves minimal energy, general position, vanishing rotation energy, and faithful distance transport. It assembles the polynomial-method genericity, the energy floor, and the transport lemmas into the form consumed by the main theorem.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L3314-L3377

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
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
