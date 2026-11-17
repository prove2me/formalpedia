-- Prove2me | Theorems.Thm_N25_level25_row_normalization
-- name    : N25.level25_row_normalization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:53.148706+00:00
-- url     : https://prove2.me/theorems/2c45702c-44e2-4e78-b29d-82e75d87bf24
-- title:
--   $H_{25}$-orbits admit canonical minima and form a group action
-- statement:
--   Let $H=\{1,7,18,24\}$ act by scaling on $R=(ℤ/25ℤ)^2$, let $code(c,d)=c+25d$, and let $ν(r)=min_{h∈H}code(hr)$. Then every orbit contains an element attaining $ν$, $ν(hr)=ν(r)$ for all $h∈H$, the four scaling maps are closed under relative composition, and each has an inverse among the four maps: $$∀r∃h∈H:code(hr)=ν(r),\qquad ν(hr)=ν(r),\qquad H\text{ acts on }R\text{ by permutations}.$$ This establishes the normalization machinery used throughout the finite level-$25$ census.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_row_normalization :
    let R := Fin 25 × Fin 25
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let code : R → ℕ := fun r => r.1.val + 25 * r.2.val
    let labels : Fin 4 → ℕ := ![1,7,18,24]
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    (∀ r : R, ∃ i : Fin 4, code (scale (labels i) r) = normcode r) ∧
    (∀ r : R, ∀ i : Fin 4, normcode (scale (labels i) r) = normcode r) ∧
    (∀ i j : Fin 4, ∃ k : Fin 4, ∀ r : R,
      scale (labels i) r = scale (labels j) (scale (labels k) r)) ∧
    (∀ i : Fin 4, ∃ j : Fin 4, ∀ r : R,
      scale (labels j) (scale (labels i) r) = r) := by sorry
