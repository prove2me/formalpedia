-- Prove2me | Theorems.Thm_N25_unitAnalytic25_gammaH
-- name    : N25.unitAnalytic25_gammaH
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:17.536173+00:00
-- url     : https://prove2.me/theorems/b0bc4585-6d8c-4e67-aa46-159a5af0c595
-- title:
--   The analytic units are invariant under the level-$25$ subgroup $Γ_H$
-- statement:
--   Let $i∈ℤ/5ℤ$, let $A$ belong to the subgroup $Γ_H(25)$ determined by $H_{25}$, and let $τ$ lie in the upper half-plane. Then $$u_i(Aτ)=u_i(τ).$$ This promotes each analytic unit to a meromorphic function on the modular curve used in the proof.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitAnalytic25_gammaH
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CohCarrier.GammaH 25 N25.H25) (τ : UpperHalfPlane) :
    unitAnalytic25 i (A • τ) = unitAnalytic25 i τ := by sorry
