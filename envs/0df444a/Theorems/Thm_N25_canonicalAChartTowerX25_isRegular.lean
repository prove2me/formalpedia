-- Prove2me | Theorems.Thm_N25_canonicalAChartTowerX25_isRegular
-- name    : N25.canonicalAChartTowerX25_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:26.429227+00:00
-- url     : https://prove2.me/theorems/7fba4ae6-5861-409f-8d08-3f65bc9821a3
-- title:
--   The image of the base coordinate $x$ is regular in the canonical chart tower
-- statement:
--   In the tower presentation of the canonical $A$-chart ring, quotient first by the linear remainder relation and consider the image of the base coordinate $x$. Then $$\operatorname{Regular}(\bar x).$$ This provides one of the non-zero-divisors whose product defines the principal open.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance xSpecialization_semiring_ida1b5f : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartTowerX25_isRegular :
    IsRegular (Ideal.Quotient.mk _
      (AdjoinRoot.of (canonicalAChartQuadratic25 K) (canonicalAChartBaseX25 K)) :
        CanonicalAChartTowerRing25 K) := by sorry
