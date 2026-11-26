-- Prove2me | Theorems.Thm_OpenQuantumProblem35_card_config
-- name    : OpenQuantumProblem35.card_config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:59.190247+00:00
-- url     : https://prove2.me/theorems/c1b18896-d310-5472-8648-44720276488d
-- title:
--   Open Quantum Problem35: card config
-- statement:
--   The number of computational-basis configurations on $m$ parties of local dimension $d$ is $d^m$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L276-L277
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L276-L277

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.card_config (m d : ℕ) : Fintype.card (Config m d) = d ^ m := by sorry
