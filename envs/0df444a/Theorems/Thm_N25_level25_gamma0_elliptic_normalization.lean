-- Prove2me | Theorems.Thm_N25_level25_gamma0_elliptic_normalization
-- name    : N25.level25_gamma0_elliptic_normalization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:04.891987+00:00
-- url     : https://prove2.me/theorems/bd0cc967-6c29-4a8a-ab15-6f03a6242711
-- title:
--   $Γ_0(25)$ elliptic orbits attain canonical minima
-- statement:
--   Let $R=(ℤ/25ℤ)^2$, call $r=(c,d)$ primitive when at least one coordinate is a unit, and define $N(c,d)=(1,c^{-1}d)$ when $c$ is a unit and $N(c,d)=(d^{-1}c,1)$ otherwise. Let $code(c,d)=c+25d$, $S(c,d)=(d,-c)$, and $ST(c,d)=(d,d-c)$. Put $s_0(r)=min(code(Nr),code(N(Sr)))$ and $t_0(r)=min(code(Nr),code(N(STr)),code(N((ST)^2r)))$. For every primitive $r$, the two displayed minima are attained within the corresponding two- and three-element orbits, and $$s_0(Sr)=s_0(r),\qquad t_0(STr)=t_0(r),$$ while $S$ and $ST$ preserve primitivity. This produces canonical representatives for the $Γ_0(25)$ elliptic double cosets.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_gamma0_elliptic_normalization :
    let R := ZMod 25 × ZMod 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let normal : R → R := fun r =>
      if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let S : R → R := fun r => (r.2,-r.1)
    let ST : R → R := fun r => (r.2,r.2-r.1)
    let snorm : R → ℕ := fun r => min (code (normal r)) (code (normal (S r)))
    let stnorm : R → ℕ := fun r =>
      min (code (normal r)) (min (code (normal (ST r))) (code (normal (ST (ST r)))))
    (∀ r : R, primitive r → ∃ n : Fin 2,
      code (normal (if n.val=0 then r else S r)) = snorm r) ∧
    (∀ r : R, primitive r → ∃ n : Fin 3,
      code (normal (if n.val=0 then r else if n.val=1 then ST r else ST (ST r))) = stnorm r) ∧
    (∀ r : R, primitive r → snorm (S r) = snorm r ∧ stnorm (ST r) = stnorm r ∧
      primitive (S r) ∧ primitive (ST r)) := by sorry
