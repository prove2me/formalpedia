-- Prove2me | Theorems.Thm_N25_level25_subgroup_index
-- name    : N25.level25_subgroup_index
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:40.50199+00:00
-- url     : https://prove2.me/theorems/8b9b6369-b551-4896-a3d1-c45baa45738b
-- title:
--   The subgroup $H_{25}$ has index five
-- statement:
--   For $H_{25}=⟨7⟩≤(ℤ/25ℤ)^×$, $$[(ℤ/25ℤ)^×:H_{25}]=5.$$ This gives the factor relating the indices of $Γ_H(25)$ and $Γ_0(25)$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_subgroup_index : H25.index = 5 := by sorry
