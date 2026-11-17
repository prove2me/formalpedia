-- Prove2me | Theorems.Thm_N25_canonicalAChartLinearRemainder25_mod_multiplier_isRegular
-- name    : N25.canonicalAChartLinearRemainder25_mod_multiplier_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:44.297783+00:00
-- url     : https://prove2.me/theorems/0ec22708-5f11-4605-b647-ec4ca54f4ea6
-- title:
--   The linear remainder is regular after reducing modulo the chart multiplier
-- statement:
--   Let $π:B_K→B_K/(m_K)$ be the quotient by the canonical base multiplier. In the quadratic adjoin-root algebra after applying $π$, the mapped linear remainder is a non-zero-divisor: $$\operatorname{Regular}\bigl(\operatorname{mk}_{q_π}(r_π)\bigr).$$ This is the third reduction needed for regularity of the localization element.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance multiplierQuotient_semiring_i9fbfae :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartLinearRemainder25_mod_multiplier_isRegular :
    let π : CanonicalAChartBase25 K →+*
        (CanonicalAChartBase25 K ⧸ Ideal.span ({canonicalAChartBaseMultiplier25 K} :
          Set (CanonicalAChartBase25 K))) := Ideal.Quotient.mk _
    IsRegular (AdjoinRoot.mk ((canonicalAChartQuadratic25 K).map π)
      ((canonicalAChartLinearRemainder25 K).map π)) := by sorry
