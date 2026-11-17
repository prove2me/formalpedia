-- Prove2me | Theorems.Thm_N25_level25_unit_orders
-- name    : N25.level25_unit_orders
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:43:54.697457+00:00
-- url     : https://prove2.me/theorems/1cf50938-84fc-49ed-9420-94605737316d
-- title:
--   The residue $2$ has order $20$ modulo $25$ and meets $H_{25}$ first at the fifth power
-- statement:
--   In $ℤ/25ℤ$, the unit $2$ satisfies $$2^5=7,\qquad 7^2=-1,\qquad 2^{20}=1,$$ while $2^n≠1$ for $1≤n<20$. Moreover $2^5∈H_{25}$ and $2^n∉H_{25}$ for $1≤n<5$. This determines the unit-group quotient and the associated order-five character.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_unit_orders :
    (2 : ZMod 25) ^ 5 = 7 ∧ (7 : ZMod 25)^2 = -1 ∧
    (2 : ZMod 25)^20 = 1 ∧
    (∀ n : Fin 20, n ≠ 0 → (2 : ZMod 25)^n.val ≠ 1) ∧
    ((ZMod.unitOfCoprime 2 (by decide))^5 ∈ H25) ∧
    (∀ n : Fin 5, n ≠ 0 → (ZMod.unitOfCoprime 2 (by decide))^n.val ∉ H25) := by sorry
