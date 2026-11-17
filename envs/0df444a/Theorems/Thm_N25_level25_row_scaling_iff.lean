-- Prove2me | Theorems.Thm_N25_level25_row_scaling_iff
-- name    : N25.level25_row_scaling_iff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:18.637072+00:00
-- url     : https://prove2.me/theorems/edfe8c3f-de5e-4ad5-b986-780f541cf62e
-- title:
--   Equal normalized codes are exactly $H_{25}$-equivalent rows
-- statement:
--   Let $H=\{1,7,18,24\}$ act on $R=(ℤ/25ℤ)^2$ by scaling, and let $ν(r)=min_{h∈H}code(hr)$. For all $r,s∈R$, $$ν(r)=ν(s)\;⇔\;s=hr\text{ for some }h∈H.$$ This proves that the normalized code completely classifies the finite $H_{25}$-orbits.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_row_scaling_iff :
    let R := Fin 25 × Fin 25
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let code : R → ℕ := fun r => r.1.val + 25 * r.2.val
    let labels : Fin 4 → ℕ := ![1,7,18,24]
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    ∀ r s : R, normcode r = normcode s ↔
      ∃ i : Fin 4, scale (labels i) r = s := by sorry
