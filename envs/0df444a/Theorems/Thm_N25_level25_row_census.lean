-- Prove2me | Theorems.Thm_N25_level25_row_census
-- name    : N25.level25_row_census
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:50.031434+00:00
-- url     : https://prove2.me/theorems/bb4c9369-3ef4-4e56-9d5c-c0883cb0c750
-- title:
--   The $H_{25}$ row census has counts $600,150,10,0,80,50$
-- statement:
--   Let $R=(ℤ/25ℤ)^2$, let $R_{prim}$ be the primitive rows, let $H=\{1,7,18,24\}$ act by scaling, and let $ν(r)=min_{h∈H}code(hr)$. Let $R_H=\{r∈R_{prim}:code(r)=ν(r)\}$, $S(c,d)=(d,-c)$, and $ST(c,d)=(d,d-c)$. Then $$|R_{prim}|=600,\quad |R_H|=150,$$ $$|\{r∈R_H:Sr=hr\text{ for some }h∈H\}|=10,\quad |\{r∈R_H:STr=hr\text{ for some }h∈H\}|=0,$$ $$|\{r∈R_H:code(r)≤ν(Sr)\}|=80,$$ $$|\{r∈R_H:code(r)≤ν(STr),\ code(r)≤ν((ST)^2r)\}|=50.$$ This finite census simultaneously supplies the subgroup index and the two elliptic-orbit counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_row_census :
    let R := Fin 25 × Fin 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let code : R → ℕ := fun r => r.1.val + 25 * r.2.val
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    let canonical : R → Prop := fun r => code r = normcode r
    let rows := (Finset.univ : Finset R).filter primitive
    let reps := rows.filter canonical
    let S : R → R := fun r => (r.2, ⟨(25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let ST : R → R := fun r =>
      (r.2, ⟨(r.2.val+25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    rows.card = 600 ∧ reps.card = 150 ∧
    (reps.filter (fun r => ∃ h ∈ ([1,7,18,24] : List ℕ), scale h r = S r)).card = 10 ∧
    (reps.filter (fun r => ∃ h ∈ ([1,7,18,24] : List ℕ), scale h r = ST r)).card = 0 ∧
    (reps.filter (fun r => code r ≤ normcode (S r))).card = 80 ∧
    (reps.filter (fun r => code r ≤ normcode (ST r) ∧
      code r ≤ normcode (ST (ST r)))).card = 50 := by sorry
