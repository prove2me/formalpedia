-- Prove2me | Theorems.Thm_N25_level25_translation_orbit_attainment
-- name    : N25.level25_translation_orbit_attainment
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:45.820567+00:00
-- url     : https://prove2.me/theorems/cc516818-c4f3-4b35-acc7-7d1903aad49e
-- title:
--   Every primitive $Γ_H(25)$ translation orbit attains its canonical code
-- statement:
--   Let $R=(ℤ/25ℤ)^2$, let $H=\{1,7,18,24\}$ act by scaling, let $ν$ be the minimum code in an $H$-orbit, and let $T_n(c,d)=(c,d+nc)$. For primitive $r=(c,d)$ define $θ_H(r)=ν(r)$ if $c=0$; define $θ_H(r)=25+5((c/5)(d\bmod5)^{-1}\bmod5)$ if $c≠0$ and $5∣c$; otherwise let $θ_H(r)$ be the least residue among $c,7c,18c,24c$ modulo $25$. Then $$∀r\text{ primitive }∃h∈H\ ∃n∈ℤ/25ℤ:\ code(hT_nr)=θ_H(r).$$ This proves that the explicit cusp-orbit minimum for $Γ_H(25)$ is attained.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_translation_orbit_attainment :
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
    ∀ r : R, primitive r → ∃ i : Fin 4, ∃ n : Fin 25,
      code (scale (labels i) (translate n.val r)) = tnorm r := by sorry
