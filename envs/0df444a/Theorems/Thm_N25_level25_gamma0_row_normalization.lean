-- Prove2me | Theorems.Thm_N25_level25_gamma0_row_normalization
-- name    : N25.level25_gamma0_row_normalization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:33.889395+00:00
-- url     : https://prove2.me/theorems/679b9aa9-f2c7-4557-8486-6caeb0233433
-- title:
--   Every primitive row has an idempotent $Γ_0(25)$ normalization
-- statement:
--   Let $r=(c,d)∈(ℤ/25ℤ)^2$ be primitive, and define $N(r)=(1,c^{-1}d)$ when $c$ is a unit and $N(r)=(d^{-1}c,1)$ otherwise. Then there exists a unit $u∈(ℤ/25ℤ)^×$ with $ur=N(r)$, and $$N(r)\text{ is primitive},\qquad N(N(r))=N(r).$$ This selects a canonical representative of each unit-scaling orbit used for $Γ_0(25)$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_gamma0_row_normalization :
    let R := ZMod 25 × ZMod 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let normal : R → R := fun r =>
      if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    ∀ r : R, primitive r →
      (∃ u : (ZMod 25)ˣ, ((u:ZMod 25)*r.1,(u:ZMod 25)*r.2) = normal r) ∧
      primitive (normal r) ∧ normal (normal r) = normal r := by sorry
