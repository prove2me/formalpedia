-- Prove2me | Theorems.Thm_N25_LocalFive_isUnit_seventyOne
-- name    : N25.LocalFive.isUnit_seventyOne
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:00.304537+00:00
-- url     : https://prove2.me/theorems/a672cce0-0944-4882-a8f0-58f0df1c2d9f
-- title:
--   $71$ is a unit in the $5$-adic integers
-- statement:
--   Let $R_5=ℤ_5$. Since $71$ is prime to $5$, its image in $R_5$ is invertible: $$(71:R_5)\in R_5^×.$$ This is the coprimality input for surjectivity of multiplication by $71$ on the reduction kernel.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveArithmetic

noncomputable section
local instance instL_N25_LocalFive_isUnit_seventyOne_bfd51b_i99d4d7 : Fact (Nat.Prime 5) := ⟨by decide⟩
open N25
open N25.LocalFive

theorem N25.LocalFive.isUnit_seventyOne : IsUnit (71 : R5)  := by sorry
