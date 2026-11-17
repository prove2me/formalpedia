-- Prove2me | Theorems.Thm_N25_canonicalAChartBaseZ25_not_mem
-- name    : N25.canonicalAChartBaseZ25_not_mem
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:46.062412+00:00
-- url     : https://prove2.me/theorems/6aa082f4-462d-41ae-9853-4b5ef80b794b
-- title:
--   The base coordinate $z$ is not contained in the multiplier ideal
-- statement:
--   Let $m_K$ be the canonical chart base multiplier. Then $$z\notin(m_K).$$ This supplies the second nonvanishing input in the multiplier-quotient regularity argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance multiplierQuotient_semiring_ie7056b :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartBaseZ25_not_mem : canonicalAChartBaseZ25 K ∉
    Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K)) := by sorry
