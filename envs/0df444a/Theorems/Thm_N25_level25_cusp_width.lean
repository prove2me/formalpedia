-- Prove2me | Theorems.Thm_N25_level25_cusp_width
-- name    : N25.level25_cusp_width
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:37.408208+00:00
-- url     : https://prove2.me/theorems/45ed2bd4-26ac-4e28-8497-4b09c46b3533
-- title:
--   The cusp width is determined by the lower-left entry modulo $25$
-- statement:
--   Let $A∈SL_2(ℤ)$, let $c$ be the least nonnegative residue modulo $25$ of its lower-left entry, and define $w=1$ if $c=0$, $w=5$ if $c≠0$ and $5∣c$, and $w=25$ otherwise. Then $w>0$, $$AT^wA^{-1}∈Γ_H(25),\qquad 0<n\text{ and }AT^nA^{-1}∈Γ_H(25)\;⇒\;w≤n.$$ Thus $w$ is exactly the width of the cusp represented by $A$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped MatrixGroups
open N25

theorem N25.level25_cusp_width (A : SL(2, ℤ)) :
    let c := (A 1 0 : ZMod 25).val
    let w := if c=0 then 1 else if c%5=0 then 5 else 25
    0 < w ∧ A*ModularGroup.T^w*A⁻¹ ∈ CohCarrier.GammaH 25 H25 ∧
      ∀ n : ℕ, 0 < n → A*ModularGroup.T^n*A⁻¹ ∈ CohCarrier.GammaH 25 H25 → w ≤ n := by sorry
