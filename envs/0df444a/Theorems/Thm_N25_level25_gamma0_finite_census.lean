-- Prove2me | Theorems.Thm_N25_level25_gamma0_finite_census
-- name    : N25.level25_gamma0_finite_census
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:25.708124+00:00
-- url     : https://prove2.me/theorems/19b961ee-695d-459d-af4d-ded8beceb533
-- title:
--   The finite $Γ_0(25)$ row census has counts $30,16,10,6$
-- statement:
--   With $R$, primitivity, normalization $N$, and $code$ as above, let $R_0$ be the primitive rows fixed by $N$. Let $S(c,d)=(d,-c)$, $ST(c,d)=(d,d-c)$, and $T_n(c,d)=(c,d+nc)$. Then $$|R_0|=30,$$ $$|\{r∈R_0:code(r)≤code(N(Sr))\}|=16,$$ $$|\{r∈R_0:code(r)≤code(N(STr)),\ code(r)≤code(N((ST)^2r))\}|=10,$$ $$|\{r∈R_0:code(r)≤code(N(T_nr))\text{ for all }n∈ℤ/25ℤ\}|=6.$$ These finite counts yield the index, elliptic-orbit, and cusp data for $Γ_0(25)$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_gamma0_finite_census :
    let R := ZMod 25 × ZMod 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let normal : R → R := fun r =>
      if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let reps := (Finset.univ : Finset R).filter (fun r => primitive r ∧ normal r = r)
    let S : R → R := fun r => (r.2,-r.1)
    let ST : R → R := fun r => (r.2,r.2-r.1)
    let translate : Fin 25 → R → R := fun n r => (r.1,r.2+(n.val:ZMod 25)*r.1)
    reps.card = 30 ∧
    (reps.filter (fun r => code r ≤ code (normal (S r)))).card = 16 ∧
    (reps.filter (fun r => code r ≤ code (normal (ST r)) ∧
      code r ≤ code (normal (ST (ST r))))).card = 10 ∧
    (reps.filter (fun r => ∀ n : Fin 25,
      code r ≤ code (normal (translate n r)))).card = 6 := by sorry
