-- Prove2me | Theorems.Thm_N25_level25_gamma0_translation_attainment
-- name    : N25.level25_gamma0_translation_attainment
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:44.074823+00:00
-- url     : https://prove2.me/theorems/c89da424-a78d-490e-b083-b4a850ea6085
-- title:
--   Every primitive $Γ_0(25)$ translation orbit attains its canonical code
-- statement:
--   Let $r=(c,d)∈(ℤ/25ℤ)^2$ be primitive, let $N$ be the unit-scaling normalization, let $T_n(c,d)=(c,d+nc)$, and let $code(c,d)=c+25d$ using least residues. Define $θ(r)=1$ when $c$ is a unit, $θ(r)=25$ when $c=0$, and otherwise $$θ(r)=25+5\big((c/5)(d\bmod 5)^{-1}\bmod 5\big).$$ Then some $n∈ℤ/25ℤ$ satisfies $$code(N(T_nr))=θ(r).$$ This proves that the explicit translation-orbit minimum is attained.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_gamma0_translation_attainment :
    let R := ZMod 25 × ZMod 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let normal : R → R := fun r =>
      if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let translate : ℕ → R → R := fun n r => (r.1,r.2+(n:ZMod 25)*r.1)
    let tnorm : R → ℕ := fun r =>
      if r.1.val%5≠0 then 1 else if r.1=0 then 25
      else 25+5*((r.1.val/5)*((r.2.val : ZMod 5)⁻¹).val%5)
    ∀ r : R, primitive r → ∃ n : Fin 25, code (normal (translate n.val r)) = tnorm r := by sorry
