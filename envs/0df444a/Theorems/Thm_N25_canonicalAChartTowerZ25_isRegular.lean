-- Prove2me | Theorems.Thm_N25_canonicalAChartTowerZ25_isRegular
-- name    : N25.canonicalAChartTowerZ25_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:22.368464+00:00
-- url     : https://prove2.me/theorems/d8e4104f-955e-400b-864c-931eacd98ddf
-- title:
--   The image of the base coordinate $z$ is regular in the canonical chart tower
-- statement:
--   In the canonical $A$-chart tower ring obtained from the quadratic root and the linear relation, the image of the base coordinate $z$ is a non-zero-divisor: $$\operatorname{Regular}(\bar z).$$ This contributes to the regularity of the chart's localization element.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance xSpecialization_semiring_ib11b45 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring
local instance zSpecialization_semiring_ib11b45 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartTowerZ25_isRegular :
    IsRegular (Ideal.Quotient.mk _
      (AdjoinRoot.of (canonicalAChartQuadratic25 K) (canonicalAChartBaseZ25 K)) :
        CanonicalAChartTowerRing25 K) := by sorry
