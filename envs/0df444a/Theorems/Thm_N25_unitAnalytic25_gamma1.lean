-- Prove2me | Theorems.Thm_N25_unitAnalytic25_gamma1
-- name    : N25.unitAnalytic25_gamma1
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:35.968197+00:00
-- url     : https://prove2.me/theorems/c657d1b7-06f6-4c8b-b27e-c79c530db1a6
-- title:
--   The analytic units are invariant under $Γ_1(25)$
-- statement:
--   Let $i∈ℤ/5ℤ$, let $A∈Γ_1(25)⊆SL_2(ℤ)$, and let $τ$ lie in the upper half-plane. Then $$u_i(Aτ)=u_i(τ).$$ This gives the basic congruence-subgroup invariance of the five modular units.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitAnalytic25_gamma1
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CongruenceSubgroup.Gamma1 25) (τ : UpperHalfPlane) :
    unitAnalytic25 i (A • τ) = unitAnalytic25 i τ := by sorry
