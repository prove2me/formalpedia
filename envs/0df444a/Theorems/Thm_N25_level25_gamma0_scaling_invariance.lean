-- Prove2me | Theorems.Thm_N25_level25_gamma0_scaling_invariance
-- name    : N25.level25_gamma0_scaling_invariance
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:12.092131+00:00
-- url     : https://prove2.me/theorems/4c6e8d7b-611f-4ad6-bc51-a1f3321a7101
-- title:
--   $Γ_0(25)$ row normalization is invariant under unit scaling
-- statement:
--   Let $N$ be the primitive-row normalization on $(ℤ/25ℤ)^2$. For every primitive row $r$ and every unit $u∈(ℤ/25ℤ)^×$, $$N(ur)=N(r),\qquad ur\text{ is primitive}.$$ This shows that the normalization depends only on the $Γ_0(25)$ row class.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_gamma0_scaling_invariance :
    let R := ZMod 25 × ZMod 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let normal : R → R := fun r =>
      if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    ∀ r : R, primitive r → ∀ u : (ZMod 25)ˣ,
      normal ((u:ZMod 25)*r.1,(u:ZMod 25)*r.2) = normal r ∧
      primitive ((u:ZMod 25)*r.1,(u:ZMod 25)*r.2) := by sorry
