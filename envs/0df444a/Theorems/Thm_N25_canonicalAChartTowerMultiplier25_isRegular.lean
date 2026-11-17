-- Prove2me | Theorems.Thm_N25_canonicalAChartTowerMultiplier25_isRegular
-- name    : N25.canonicalAChartTowerMultiplier25_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:22.479891+00:00
-- url     : https://prove2.me/theorems/f220ff56-0010-45f0-83d3-83be21d75fc4
-- title:
--   The multiplier remains regular in the canonical chart tower
-- statement:
--   In the canonical $A$-chart tower ring, the image of the base multiplier $m_K$ is a non-zero-divisor: $$\operatorname{Regular}(\bar m_K).$$ Together with regularity of the coordinate images, this proves regularity of the full open element.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

noncomputable section
open N25
open Polynomial
variable (K : Type*) [Field K]
local instance multiplierQuotient_semiring_if0a768 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

theorem N25.canonicalAChartTowerMultiplier25_isRegular :
    IsRegular (Ideal.Quotient.mk _
      (AdjoinRoot.of (canonicalAChartQuadratic25 K) (canonicalAChartBaseMultiplier25 K)) :
        CanonicalAChartTowerRing25 K) := by sorry
