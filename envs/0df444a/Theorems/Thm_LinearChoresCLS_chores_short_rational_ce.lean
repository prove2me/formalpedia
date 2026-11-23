-- Prove2me | Theorems.Thm_LinearChoresCLS_chores_short_rational_ce
-- name    : LinearChoresCLS.chores_short_rational_ce
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:15:32.363804+00:00
-- url     : https://prove2.me/theorems/44d48e41-a819-4676-aa7a-37c5fb72ced7
-- title:
--   Short exact rational equilibria for linear chores markets
-- statement:
--   There is a fixed exponent $k$ such that every valid rational linear Fisher market with chores has an exact rational competitive equilibrium $(p,z)$ whose binary encoding has length at most $(|x|+1)^k+k$, where $x$ is the encoding of the market.
--
--   This combines equilibrium existence with the polynomial-size rational-solution bound needed for TFNP membership. The exponent is uniform over all market instances.
--
--   **Formalization Note** The assertion is `TotalSearch (bounded choresCESearch k)`; `bounded` restricts answers by precisely the displayed length bound.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e…), pp.3–4, citing Chaudhury–Garg–McGlaughlin–Mehta 2022; rational answers and encoding convention from Definition 2.2, p.6 and Proposition 4.1, p.11.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash

/-- Every valid rational linear chores market has an exact rational competitive equilibrium whose
encoding is bounded by one fixed polynomial of the instance length. -/
theorem LinearChoresCLS.chores_short_rational_ce :
    ∃ k : ℕ, TotalSearch (bounded choresCESearch k) := by sorry
