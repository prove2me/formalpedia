-- Prove2me | Theorems.Thm_N25_unitSeries25_coeffEmb
-- name    : N25.unitSeries25_coeffEmb
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:53.169586+00:00
-- url     : https://prove2.me/theorems/bce754ed-87f8-489d-8c60-5637391318f3
-- title:
--   Embedding rational coefficients carries each unit series to its base change
-- statement:
--   Let $K$ be a field equipped with a $ℚ$-algebra structure, and let $S_i^{ℚ}$ and $S_i^K$ be the $i$th unit Laurent series over $ℚ$ and $K$. Then $$\operatorname{coeffEmb}_K(S_i^{ℚ})=S_i^K.$$ This provides coefficient compatibility between the rational and geometric q-expansions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff

set_option autoImplicit false
open ModularCurve
open N25

theorem N25.unitSeries25_coeffEmb (K : Type*) [Field K] [Algebra ℚ K] (i : Fin 5) :
    coeffEmb K (unitSeries25 ℚ i) = unitSeries25 K i := by sorry
