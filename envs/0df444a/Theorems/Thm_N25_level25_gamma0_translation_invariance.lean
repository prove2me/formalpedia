-- Prove2me | Theorems.Thm_N25_level25_gamma0_translation_invariance
-- name    : N25.level25_gamma0_translation_invariance
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:53.439723+00:00
-- url     : https://prove2.me/theorems/dba8569c-2aa5-461c-8226-69af2dde7c0c
-- title:
--   The $Γ_0(25)$ translation code is invariant and characterizes minima
-- statement:
--   With primitive rows, normalization $N$, translations $T_n$, code, and $θ$ defined as in the preceding statement, $θ$ is unchanged by multiplying a primitive row by any unit, and $θ(T_1r)=θ(r)$ with $T_1r$ still primitive. Moreover, for every primitive $r$, $$code(r)=θ(r)\;⇔\;N(r)=r\text{ and }code(r)≤code(N(T_nr))\text{ for every }n∈ℤ/25ℤ.$$ This identifies exactly the canonical cusp representatives for $Γ_0(25)$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_gamma0_translation_invariance :
    let R := ZMod 25 × ZMod 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let normal : R → R := fun r =>
      if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let translate : ℕ → R → R := fun n r => (r.1,r.2+(n:ZMod 25)*r.1)
    let tnorm : R → ℕ := fun r =>
      if r.1.val%5≠0 then 1 else if r.1=0 then 25
      else 25+5*((r.1.val/5)*((r.2.val : ZMod 5)⁻¹).val%5)
    (∀ r : R, primitive r → ∀ u : (ZMod 25)ˣ,
      tnorm ((u:ZMod 25)*r.1,(u:ZMod 25)*r.2) = tnorm r) ∧
    (∀ r : R, primitive r → tnorm (translate 1 r) = tnorm r ∧ primitive (translate 1 r)) ∧
    (∀ r : R, primitive r →
      (code r = tnorm r ↔ normal r = r ∧
        ∀ n : Fin 25, code r ≤ code (normal (translate n.val r)))) := by sorry
