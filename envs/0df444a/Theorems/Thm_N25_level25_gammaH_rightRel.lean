-- Prove2me | Theorems.Thm_N25_level25_gammaH_rightRel
-- name    : N25.level25_gammaH_rightRel
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:27.805088+00:00
-- url     : https://prove2.me/theorems/3621e55d-c8d1-4b21-a126-6e1e49769540
-- title:
--   Right cosets of $Γ_H(25)$ are classified by scaled bottom rows
-- statement:
--   Let $H≤(ℤ/25ℤ)^×$ and let $A,B∈SL_2(ℤ)$. Then $A$ and $B$ lie in the same right coset modulo $Γ_H(25)$ exactly when their bottom rows modulo $25$ differ by multiplication by an element of $H$: $$A∼_{Γ_H(25)}B\;⇔\;∃u∈H:\ (B_{21},B_{22})=u(A_{21},A_{22})\text{ in }(ℤ/25ℤ)^2.$$ This turns the coset problem into the finite row-orbit computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open scoped MatrixGroups
open N25

theorem N25.level25_gammaH_rightRel (H : Subgroup (ZMod 25)ˣ) (A B : SL(2, ℤ)) :
    QuotientGroup.rightRel (CohCarrier.GammaH 25 H) A B ↔
      ∃ u : (ZMod 25)ˣ, u ∈ H ∧
        (B 1 0 : ZMod 25) = (u : ZMod 25) * (A 1 0 : ZMod 25) ∧
        (B 1 1 : ZMod 25) = (u : ZMod 25) * (A 1 1 : ZMod 25) := by sorry
