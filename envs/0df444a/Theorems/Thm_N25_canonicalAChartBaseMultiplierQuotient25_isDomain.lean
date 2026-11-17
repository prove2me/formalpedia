-- Prove2me | Theorems.Thm_N25_canonicalAChartBaseMultiplierQuotient25_isDomain
-- name    : N25.canonicalAChartBaseMultiplierQuotient25_isDomain
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:55.737238+00:00
-- url     : https://prove2.me/theorems/9be99975-7e1e-4ca9-98ee-58f1bbddc1be
-- title:
--   The chart base modulo the multiplier is an integral domain
-- statement:
--   Let $B_K$ be the canonical $A$-chart base ring and let $m_K$ be its distinguished multiplier. Then $$B_K/(m_K)\text{ is an integral domain}.$$ This supports the regularity test for the remaining relation modulo the multiplier.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance multiplierQuotient_semiring_i2705ca :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartBaseMultiplierQuotient25_isDomain :
    IsDomain (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) := by sorry
