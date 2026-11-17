-- Prove2me | Theorems.Thm_N25_canonicalAChartBaseMultiplier25_irreducible
-- name    : N25.canonicalAChartBaseMultiplier25_irreducible
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:27.008868+00:00
-- url     : https://prove2.me/theorems/f020b26d-4632-4cf7-963a-128a557f950b
-- title:
--   The base multiplier polynomial of the canonical chart is irreducible
-- statement:
--   Let $m_K$ be the distinguished multiplier element in the canonical $A$-chart base ring. Then $$m_K\text{ is irreducible}.$$ This is the algebraic input for proving that the multiplier defines a prime divisor.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance multiplierQuotient_semiring_i50a102 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartBaseMultiplier25_irreducible :
    Irreducible (canonicalAChartBaseMultiplier25 K) := by sorry
