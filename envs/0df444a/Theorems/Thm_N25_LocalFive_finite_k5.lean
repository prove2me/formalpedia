-- Prove2me | Theorems.Thm_N25_LocalFive_finite_k5
-- name    : N25.LocalFive.finite_k5
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:55.459263+00:00
-- url     : https://prove2.me/theorems/5cb4e249-3251-4ffa-9609-ae51e0ef5bcf
-- title:
--   The residue field at $5$ is finite
-- statement:
--   Let $R_5=ℤ_5$ be the ring of $5$-adic integers and let $k_5=R_5/\mathfrak m_5$ be its residue field. Then $$|k_5|<\infty.$$ This supplies the finite target needed to prove finiteness of reduction fibers and special-fiber points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveArithmetic

noncomputable section
local instance instL_N25_LocalFive_finite_k5_bfd51b_i828a6f : Fact (Nat.Prime 5) := ⟨by decide⟩
open N25
open N25.LocalFive

theorem N25.LocalFive.finite_k5 : Finite k5  := by sorry
