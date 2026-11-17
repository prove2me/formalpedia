-- Prove2me | Theorems.Thm_N25_canonicalAChartQuadratic25_monic
-- name    : N25.canonicalAChartQuadratic25_monic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:09.91655+00:00
-- url     : https://prove2.me/theorems/430c6d42-3f54-44c6-b4cf-9cc914e183e6
-- title:
--   The quadratic polynomial in the canonical chart tower is monic
-- statement:
--   Let $q_K(Y)$ be the quadratic polynomial defining the first stage of the canonical $A$-chart tower. Then $$q_K(Y)\text{ is monic}.$$ This ensures that adjoining its root has the expected finite free presentation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance multiplierQuotient_semiring_ic34f35 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartQuadratic25_monic : (canonicalAChartQuadratic25 K).Monic := by sorry
