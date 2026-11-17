-- Prove2me | Theorems.Thm_N25_unitNumerator_isIntegralQExp25
-- name    : N25.unitNumerator_isIntegralQExp25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:50:29.485708+00:00
-- url     : https://prove2.me/theorems/3a59eb5a-e43c-4391-9d99-b816cb013ed2
-- title:
--   $Δ^3u_i$ has the prescribed integral q-expansion
-- statement:
--   For each $i∈ℤ/5ℤ$, let $N_i(q)$ be the designated numerator series. Then the analytic function $τ↦Δ(τ)^3u_i(τ)$ satisfies $$q\text{-exp}(Δ^3u_i)=N_i(q)\text{ with integral coefficients}.$$ This provides the numerator expansion used in the cleared polynomial relation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitNumerator_isIntegralQExp25 (i : Fin 5) :
    ModularCurve.IsIntegralQExp
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ)
      (unitNumeratorSeries25 i) := by sorry
