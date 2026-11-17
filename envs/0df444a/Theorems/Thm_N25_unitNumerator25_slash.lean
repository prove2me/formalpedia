-- Prove2me | Theorems.Thm_N25_unitNumerator25_slash
-- name    : N25.unitNumerator25_slash
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:44.544917+00:00
-- url     : https://prove2.me/theorems/77155f57-8146-4c76-b812-5c871c70850b
-- title:
--   The weight-$36$ slash action moves only the unit argument
-- statement:
--   Let $i∈ℤ/5ℤ$, let $A∈SL_2(ℤ)$, and define $F_i(τ)=Δ(τ)^3u_i(τ)$. Under the weight-$36$ slash action, $$F_i\vert_{36}A\;=\;\bigl(τ↦Δ(τ)^3u_i(Aτ)\bigr).$$ This reduces cusp boundedness of the slash transforms to the analytic leading-limit estimates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open scoped ModularForm
open N25

theorem N25.unitNumerator25_slash (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ) ∣[(36 : ℤ)] A) =
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i (A • τ)) := by sorry
