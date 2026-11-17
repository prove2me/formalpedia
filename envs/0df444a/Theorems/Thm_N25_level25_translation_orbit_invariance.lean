-- Prove2me | Theorems.Thm_N25_level25_translation_orbit_invariance
-- name    : N25.level25_translation_orbit_invariance
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:50.995881+00:00
-- url     : https://prove2.me/theorems/b59d3c80-9f23-403f-bfe9-21208bdbce35
-- title:
--   The $Γ_H(25)$ translation code is invariant and detects canonical rows
-- statement:
--   With $H$, $ν$, $T_n$, and $θ_H$ as in the preceding statement, $θ_H$ is invariant under $H$-scaling and under $T_1$, and these operations preserve primitivity. For every primitive row $r$, $$code(r)=θ_H(r)\;⇔\;code(r)≤ν(T_nr)\text{ for every }n∈ℤ/25ℤ.$$ This characterizes the canonical cusp representatives used in the width census.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_translation_orbit_invariance :
    let R := Fin 25 × Fin 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let labels : Fin 4 → ℕ := ![1,7,18,24]
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    let translate : ℕ → R → R := fun n r =>
      (r.1, ⟨(r.2.val+n*r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let tnorm : R → ℕ := fun r =>
      if r.1.val=0 then normcode r
      else if r.1.val%5=0 then
        25 + 5 * ((r.1.val/5) * ((r.2.val : ZMod 5)⁻¹).val % 5)
      else min (min r.1.val (7*r.1.val%25))
        (min (18*r.1.val%25) (24*r.1.val%25))
    (∀ r : R, primitive r → ∀ i : Fin 4,
      tnorm (scale (labels i) r) = tnorm r ∧
      (primitive (scale (labels i) r) ↔ primitive r)) ∧
    (∀ r : R, primitive r → tnorm (translate 1 r) = tnorm r ∧
      (primitive (translate 1 r) ↔ primitive r)) ∧
    (∀ r : R, primitive r →
      (code r = tnorm r ↔ ∀ n : Fin 25, code r ≤ normcode (translate n.val r))) := by sorry
