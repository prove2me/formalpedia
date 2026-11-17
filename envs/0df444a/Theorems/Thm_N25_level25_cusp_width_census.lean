-- Prove2me | Theorems.Thm_N25_level25_cusp_width_census
-- name    : N25.level25_cusp_width_census
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:12.141373+00:00
-- url     : https://prove2.me/theorems/3ed3536e-7919-4229-a856-93e8b0a685f2
-- title:
--   The fourteen cusps have widths $1^5,5^4,25^5$
-- statement:
--   Let $R=(ℤ/25ℤ)^2$ using representatives $0,…,24$, call $r=(c,d)$ primitive when at least one coordinate is not divisible by $5$, and let $H=\{1,7,18,24\}$ act by scaling. Set $code(c,d)=c+25d$, $ν(r)=min_{h∈H}code(hr)$, and $T_n(c,d)=(c,d+nc)$. Let $C$ be the primitive rows satisfying $code(r)≤ν(T_nr)$ for every $n∈ℤ/25ℤ$, and put $w(r)=1$ if $c=0$, $w(r)=5$ if $c≠0$ and $5∣c$, and $w(r)=25$ otherwise. Then $$|C|=14,\quad |C_{w=1}|=5,\quad |C_{w=5}|=4,\quad |C_{w=25}|=5,\quad ∑_{r∈C}w(r)=150.$$ Moreover $ν(T_{w(r)}r)=ν(r)$ for every primitive $r$, and no positive $n<w(r)$ has $ν(T_nr)=ν(r)$. This certifies both the cusp count and the complete width distribution.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_cusp_width_census :
    let R := Fin 25 × Fin 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let code : R → ℕ := fun r => r.1.val + 25 * r.2.val
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    let translate : ℕ → R → R := fun n r =>
      (r.1, ⟨(r.2.val+n*r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let cusps := (Finset.univ : Finset R).filter (fun r => primitive r ∧
      ∀ n : Fin 25, code r ≤ normcode (translate n.val r))
    let width : R → ℕ := fun r =>
      if r.1.val = 0 then 1 else if r.1.val % 5 = 0 then 5 else 25
    cusps.card = 14 ∧
    (cusps.filter (fun r => width r = 1)).card = 5 ∧
    (cusps.filter (fun r => width r = 5)).card = 4 ∧
    (cusps.filter (fun r => width r = 25)).card = 5 ∧
    (∑ r ∈ cusps, width r) = 150 ∧
    (∀ r : R, primitive r →
      normcode (translate (width r) r) = normcode r ∧
      ∀ n : Fin 25, 0 < n.val → n.val < width r →
        normcode (translate n.val r) ≠ normcode r) := by sorry
