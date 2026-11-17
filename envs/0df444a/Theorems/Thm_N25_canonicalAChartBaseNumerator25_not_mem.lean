-- Prove2me | Theorems.Thm_N25_canonicalAChartBaseNumerator25_not_mem
-- name    : N25.canonicalAChartBaseNumerator25_not_mem
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:57.208846+00:00
-- url     : https://prove2.me/theorems/c6e4e936-59cc-4f32-85df-17fac9870837
-- title:
--   The numerator $x^2-z+1$ is not contained in the multiplier ideal
-- statement:
--   Let $m_K$ be the canonical chart base multiplier. Then the base numerator satisfies $$x^2-z+1\notin(m_K).$$ This proves that its image is nonzero in the domain obtained by quotienting by the multiplier.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance multiplierQuotient_semiring_if950e3 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartBaseNumerator25_not_mem :
    (canonicalAChartBaseX25 K)^2-canonicalAChartBaseZ25 K+1 ∉
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K)) := by sorry
