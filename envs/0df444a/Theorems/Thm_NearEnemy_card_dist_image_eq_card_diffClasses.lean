-- Prove2me | Theorems.Thm_NearEnemy_card_dist_image_eq_card_diffClasses
-- name    : NearEnemy.card_dist_image_eq_card_diffClasses
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-18T14:54:42.67054+00:00
-- url     : https://prove2.me/theorems/9cb9401c-96bf-43e4-8d64-3bad9e3f50d4
-- title:
--   Under difference separation, the projected distance count equals the sign-paired difference-class count
-- statement:
--   Let $G$ be a finite point set in `EuclideanSpace ℝ ι` and $T$ a real-linear map to the plane satisfying the separation hypothesis `hsep`: whenever $a,b,c,e \in G$ with $a-b \neq c-e$ and $a-b \neq -(c-e)$, the projected distances differ, $\operatorname{dist}(Ta,Tb) \neq \operatorname{dist}(Tc,Te)$. Then the number of distinct projected distances over ordered off-diagonal pairs equals the number of sign-paired difference classes in the source:
--
--   $$\big|\{\operatorname{dist}(q_1,q_2) : q \in (T(G))^{\neq}\}\big| = \big|\{\{p_1-p_2,\,p_2-p_1\} : p \in G^{\neq}\}\big|.$$
--
--   Here $G^{\neq}$ denotes `Finset.offDiag` (ordered pairs of distinct points). This counting identity is the quantitative form of distance transport: under the separation hypothesis no two unrelated source differences collide after projection, so the set of projected distances faithfully records the source difference classes. It is used to control the distance profile of the minimal-energy image.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, footnote 1 on p. 538, state that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1); the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The generic planar projection that is injective, keeps general position and transports distances is Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L1725-L1816

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

theorem NearEnemy.card_dist_image_eq_card_diffClasses {G : Finset (EuclideanSpace ℝ ι)}
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hsep : ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
      a - b ≠ c - e → a - b ≠ -(c - e) →
      dist (T a) (T b) ≠ dist (T c) (T e)) :
    (((G.image fun x ↦ T x).offDiag).image fun q ↦ dist q.1 q.2).card =
      ((G.offDiag).image fun p ↦
        ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι))).card := by sorry
