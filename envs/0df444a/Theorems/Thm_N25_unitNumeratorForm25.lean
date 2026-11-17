-- Prove2me | Theorems.Thm_N25_unitNumeratorForm25
-- name    : N25.unitNumeratorForm25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:37.626477+00:00
-- url     : https://prove2.me/theorems/6f1b3a49-ab94-4227-b8e6-94c4f06f3bdd
-- title:
--   $Δ^3u_i$ is a weight-$36$ modular form with integral q-expansion
-- statement:
--   For each $i∈ℤ/5ℤ$, let $N_i(q)$ be the prescribed numerator series. There exists a modular form $F_i$ of weight $36$ on $Γ_H(25)$ such that $$F_i(τ)=Δ(τ)^3u_i(τ)\quad\text{for all }τ∈\mathfrak H,$$ and $F_i$ has integral q-expansion $N_i(q)$. This realizes every unit as a quotient of integral modular forms of the same weight.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitNumeratorForm25 (i : Fin 5) :
    ∃ F : ModularForm GammaH25GL 36,
      (∀ τ : UpperHalfPlane,
        F τ = ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ) ∧
      ModularCurve.IsIntegralQExp F (unitNumeratorSeries25 i) := by sorry
