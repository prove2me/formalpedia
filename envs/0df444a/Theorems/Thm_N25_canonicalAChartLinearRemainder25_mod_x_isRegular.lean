-- Prove2me | Theorems.Thm_N25_canonicalAChartLinearRemainder25_mod_x_isRegular
-- name    : N25.canonicalAChartLinearRemainder25_mod_x_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:41.959304+00:00
-- url     : https://prove2.me/theorems/9034fd4a-df59-498e-9277-91b859c87c0a
-- title:
--   The linear remainder is regular after reducing the chart base modulo $x$
-- statement:
--   Let $π$ be the quotient map from the canonical $A$-chart base ring to its quotient by the ideal $(x)$. In the corresponding quadratic adjoin-root algebra, the image of the chart's linear remainder is a non-zero-divisor: $$\operatorname{Regular}\bigl(\operatorname{mk}_{q_π}(r_π)\bigr).$$ This is one of the regular-sequence checks used to prove the chart ring is a domain.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance xSpecialization_semiring_ie5bc96 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartLinearRemainder25_mod_x_isRegular :
    let π : CanonicalAChartBase25 K →+* (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
      Ideal.Quotient.mk _
    IsRegular (AdjoinRoot.mk ((canonicalAChartQuadratic25 K).map π)
      ((canonicalAChartLinearRemainder25 K).map π)) := by sorry
