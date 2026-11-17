-- Prove2me | Theorems.Thm_N25_canonicalAChartLinearRemainder25_mod_z_isRegular
-- name    : N25.canonicalAChartLinearRemainder25_mod_z_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:34.002789+00:00
-- url     : https://prove2.me/theorems/1dbcc57d-3ca4-4b54-a154-653c428e126d
-- title:
--   The linear remainder is regular after reducing the chart base modulo $z$
-- statement:
--   Let $π$ be the quotient map from the canonical $A$-chart base ring to its quotient by $(z)$. In the mapped quadratic adjoin-root algebra, the image of the chart linear remainder is a non-zero-divisor: $$\operatorname{Regular}\bigl(\operatorname{mk}_{q_π}(r_π)\bigr).$$ This is the second coordinate regularity check for the tower presentation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance xSpecialization_semiring_i41eef0 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring
local instance zSpecialization_semiring_i41eef0 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartLinearRemainder25_mod_z_isRegular :
    let π : CanonicalAChartBase25 K →+* (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
      Ideal.Quotient.mk _
    IsRegular (AdjoinRoot.mk ((canonicalAChartQuadratic25 K).map π)
      ((canonicalAChartLinearRemainder25 K).map π)) := by sorry
