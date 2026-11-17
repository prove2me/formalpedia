-- Prove2me | Theorems.Thm_N25_level25_elliptic_orbit_normalization
-- name    : N25.level25_elliptic_orbit_normalization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:20.042952+00:00
-- url     : https://prove2.me/theorems/a7372757-e8f5-4582-b4a7-e563cf8f3e07
-- title:
--   The $S$- and $ST$-orbits admit canonical level-$25$ representatives
-- statement:
--   Let $R=(ℤ/25ℤ)^2$, let primitive rows be those not divisible by $5$ in both coordinates, let $H=\{1,7,18,24\}$ act by scaling, and let $ν$ be the minimum encoded value in an $H$-orbit. Define $S(c,d)=(d,-c)$ and $ST(c,d)=(d,d-c)$, and set $s(r)=min(ν(r),ν(Sr))$ and $t(r)=min(ν(r),ν(STr),ν((ST)^2r))$. For every primitive $r$, these minima are attained by an $H$-multiple of one of the two $S$-orbit points and one of the three $ST$-orbit points, respectively. In addition, $$s(hr)=s(r),\quad t(hr)=t(r),\quad s(Sr)=s(r),\quad t(STr)=t(r),$$ and the actions of $H$, $S$, and $ST$ preserve primitivity. This provides canonical finite representatives for the elliptic double-coset counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_elliptic_orbit_normalization :
    let R := Fin 25 × Fin 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let labels : Fin 4 → ℕ := ![1,7,18,24]
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    let S : R → R := fun r => (r.2, ⟨(25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let ST : R → R := fun r =>
      (r.2, ⟨(r.2.val+25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let snorm : R → ℕ := fun r => min (normcode r) (normcode (S r))
    let stnorm : R → ℕ := fun r =>
      min (normcode r) (min (normcode (ST r)) (normcode (ST (ST r))))
    (∀ r : R, primitive r →
      ∃ i : Fin 4, ∃ n : Fin 2,
        code (scale (labels i) (if n.val=0 then r else S r)) = snorm r) ∧
    (∀ r : R, primitive r →
      ∃ i : Fin 4, ∃ n : Fin 3,
        code (scale (labels i) (if n.val=0 then r else if n.val=1 then ST r else ST (ST r))) = stnorm r) ∧
    (∀ r : R, ∀ i : Fin 4,
      snorm (scale (labels i) r) = snorm r ∧
      stnorm (scale (labels i) r) = stnorm r ∧
      (primitive (scale (labels i) r) ↔ primitive r)) ∧
    (∀ r : R, snorm (S r) = snorm r ∧ stnorm (ST r) = stnorm r ∧
      (primitive (S r) ↔ primitive r) ∧ (primitive (ST r) ↔ primitive r)) := by sorry
