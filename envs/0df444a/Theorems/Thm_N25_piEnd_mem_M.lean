-- Prove2me | Theorems.Thm_N25_piEnd_mem_M
-- name    : N25.piEnd_mem_M
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:10.517045+00:00
-- url     : https://prove2.me/theorems/befc4b5a-b596-48d4-9dfc-a8a6d955f8ad
-- title:
--   The selected endomorphism preserves rational fixed points
-- statement:
--   Let $M=J^{G_{ℚ}}$ and $π=2+4γ+γ^2$. For every $x∈J$, $$x∈M\quad⇒\quad πx∈M.$$ This defines the endomorphism used on the rational Mordell–Weil subgroup.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm

set_option autoImplicit false
open N25

theorem N25.piEnd_mem_M {x : N25.J} (hx : x ∈ N25.M) : N25.piEnd x ∈ N25.M := by sorry
