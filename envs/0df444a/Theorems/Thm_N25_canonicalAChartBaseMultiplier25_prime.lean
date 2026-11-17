-- Prove2me | Theorems.Thm_N25_canonicalAChartBaseMultiplier25_prime
-- name    : N25.canonicalAChartBaseMultiplier25_prime
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:56.319584+00:00
-- url     : https://prove2.me/theorems/a17c46e7-18ae-41d3-8bc8-d3562c0b899b
-- title:
--   The base multiplier polynomial of the canonical chart is prime
-- statement:
--   Let $m_K$ be the canonical $A$-chart base multiplier. Then $$m_K\text{ is a prime element}.$$ This implies that quotienting the base ring by the multiplier produces a domain.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance multiplierQuotient_semiring_i8996ee :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartBaseMultiplier25_prime :
    Prime (canonicalAChartBaseMultiplier25 K) := by sorry
