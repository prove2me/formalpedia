-- Prove2me | Theorems.Thm_N25_unitNumerator25_bounded_product
-- name    : N25.unitNumerator25_bounded_product
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:46.788427+00:00
-- url     : https://prove2.me/theorems/ff00264c-a0c6-4edc-890b-f45056ea990d
-- title:
--   $Δ^3$ times every transformed unit is bounded at the cusp
-- statement:
--   Let $i∈ℤ/5ℤ$ and $A∈SL_2(ℤ)$. The function on the upper half-plane given by $τ↦Δ(τ)^3u_i(Aτ)$ satisfies $$Δ(τ)^3u_i(Aτ)\text{ is bounded as }\operatorname{Im}τ→∞.$$ This is the cusp-holomorphy input for the numerator modular form.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitNumerator25_bounded_product
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 *
        unitAnalytic25 i (A • τ)) := by sorry
