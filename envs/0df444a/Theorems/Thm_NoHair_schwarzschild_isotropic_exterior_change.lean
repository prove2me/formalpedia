-- Prove2me | Theorems.Thm_NoHair_schwarzschild_isotropic_exterior_change
-- name    : NoHair.schwarzschild_isotropic_exterior_change
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:27:47.284051+00:00
-- url     : https://prove2.me/theorems/71beb92f-222b-4364-9976-00b341bbbbd2
-- title:
--   Global Schwarzschild exterior change from Kerr–Schild to isotropic coordinates
-- statement:
--   Let $b>0$ and put $m=2b$. The Schwarzschild Kerr–Schild exterior $r>4b$ is diffeomorphic to the isotropic exterior $\rho>b$, equivalently the positive-lapse side of $U(\rho)=1+b/\rho$. Under this diffeomorphism the pullback of $-(2/U-1)^2 d\tau^2+U^4 dx\cdot dx$ agrees in every component with the Schwarzschild Kerr–Schild metric.
--
--   On the outer isotropic branch $r=\rho(1+b/\rho)^2$. The time shift from the Kerr–Schild time $t$ to static time is $\tau=t-4b\log(r-4b)$, up to an additive constant.
-- source:
--   Standard Schwarzschild exterior coordinate relations, S. Carroll, Lecture Notes on General Relativity, Section 7, https://arxiv.org/abs/gr-qc/9712019. The areal and isotropic relations are also recorded in the Prove2Me ExactVacuumAtlas Schwarzschild isotropic modules.

import Definitions.Def_NoHair_conformalVacuumExterior

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.schwarzschild_isotropic_exterior_change (b : ℝ) (hb : 0 < b) :
    let U := fun x : EuclideanSpace ℝ (Fin 3) => 1 + b / ‖x‖
    ∃ H : E4 → E4, IsDiffeoOnto H (kerrNewmanDOC (2 * b) 0 0) (conformalExteriorDomain U) ∧
      ∀ y ∈ kerrNewmanDOC (2 * b) 0 0, ∀ i j : Fin 4,
        conformalStaticForm (U (conformalSpatialPoint (H y)))
          (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) H y (coordBasis i))
          (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) H y (coordBasis j)) =
          kerrNewmanMetric (2 * b) 0 0 y i j := by sorry
