-- Prove2me | Theorems.Thm_NearEnemy_nearEnemy_noThreeCollinear_exists_projectionGeneric_image_generalPosition_rotationFree
-- name    : NearEnemy.nearEnemy_noThreeCollinear_exists_projectionGeneric_image_generalPosition_rotationFree
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:55:11.068808+00:00
-- url     : https://prove2.me/theorems/4b0cdcd7-2d88-4bf9-a068-80b1efeed3eb
-- title:
--   Generic rotation-free projection preserving general position
-- statement:
--   Let $G$ be a finite set in `EuclideanSpace ℝ ι` with no three collinear. Then there exists a real-linear map $T$ to the plane such that: (i) `ProjectionGeneric T G` holds; (ii) images of distinct triples of $G$ remain non-collinear; (iii) images of distinct quadruples remain non-cospherical; (iv) the distance-separation property holds, i.e. for $a,b,c,e \in G$,
--
--   $$a - b \neq c - e\ \land\ a - b \neq -(c - e)\ \Longrightarrow\ \operatorname{dist}(Ta,Tb) \neq \operatorname{dist}(Tc,Te).$$
--
--   This is the existence theorem for the generic projection itself, the single witness whose degeneracy-avoidance (built one nonzero polynomial at a time: `innerPoly`, `circPoly`, and separation conditions) underlies the energy-minimal, rotation-free, general-position image. Every downstream bundle theorem instantiates this $T$.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L2650-L2859

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.nearEnemy_noThreeCollinear_exists_projectionGeneric_image_generalPosition_rotationFree {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      ProjectionGeneric T G ∧
      (∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
        ¬ Collinear ℝ ({T p₁, T p₂, T p₃} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, ∀ p₄ ∈ G,
        p₁ ≠ p₂ → p₁ ≠ p₃ → p₁ ≠ p₄ → p₂ ≠ p₃ → p₂ ≠ p₄ → p₃ ≠ p₄ →
        ¬ EuclideanGeometry.Cospherical
          ({T p₁, T p₂, T p₃, T p₄} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
        a - b ≠ c - e → a - b ≠ -(c - e) →
        dist (T a) (T b) ≠ dist (T c) (T e) := by sorry
