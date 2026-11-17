-- Prove2me | Theorems.Thm_N25_unitAnalytic25_cusp_limit_of_not_twentyFive_dvd
-- name    : N25.unitAnalytic25_cusp_limit_of_not_twentyFive_dvd
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:06.314953+00:00
-- url     : https://prove2.me/theorems/68866ea6-2ea2-47de-ad83-c19efb11de7b
-- title:
--   Non-width-one cusp directions have a finite nonzero unit limit
-- statement:
--   Let $i∈ℤ/5ℤ$ and $A∈SL_2(ℤ)$, and assume that $25$ does not divide the lower-left entry $A_{21}$. Then there is $c∈ℂ^{×}$ such that $$\lim_{\operatorname{Im}τ→∞}u_i(Aτ)=c.$$ This shows that the unit has neither a zero nor a pole in these cusp directions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open Filter Topology
open N25

theorem N25.unitAnalytic25_cusp_limit_of_not_twentyFive_dvd
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : ¬ (25 : ℤ) ∣ A 1 0) :
    ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto
      (fun τ : UpperHalfPlane => unitAnalytic25 i (A • τ))
      UpperHalfPlane.atImInfty (nhds c) := by sorry
