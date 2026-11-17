-- Prove2me | Theorems.Thm_N25_unitDenominatorSeries25_ne_zero
-- name    : N25.unitDenominatorSeries25_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:37.179545+00:00
-- url     : https://prove2.me/theorems/d69aa3d9-14f3-4731-95fb-cf7ec5abf125
-- title:
--   The common denominator q-series remains nonzero over every field
-- statement:
--   Let $K$ be a field, and let $D_K$ be the Laurent series obtained from the integral denominator series by mapping its coefficients to $K$. Then $$D_K≠0.$$ This licenses division by the denominator after arbitrary coefficient-field change.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25

theorem N25.unitDenominatorSeries25_ne_zero (K : Type*) [Field K] :
    ModularCurve.intSeriesC K unitDenominatorSeries25 ≠ 0 := by sorry
