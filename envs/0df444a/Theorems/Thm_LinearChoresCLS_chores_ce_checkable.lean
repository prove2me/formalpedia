-- Prove2me | Theorems.Thm_LinearChoresCLS_chores_ce_checkable
-- name    : LinearChoresCLS.chores_ce_checkable
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:17:35.146099+00:00
-- url     : https://prove2.me/theorems/8f96ae56-0bae-4610-a8a3-da715bb5a37c
-- title:
--   Polynomial-time verification of bounded linear chores equilibria
-- statement:
--   For every fixed answer-length exponent $k$, one can verify in polynomial time whether a binary string $x$ encodes a valid rational linear chores market and whether a binary string $y$ encodes an exact rational competitive equilibrium of that market satisfying $|y|\le(|x|+1)^k+k$.
--
--   The verification includes positivity of the market data, nonnegativity and earning feasibility of allocations, global optimality within each agent's linear demand problem, market clearing, and the answer-length test.
--
--   **Formalization Note** Polynomial time is on Cook's machines, using the public `checkLang` pair encoding and the relation of `bounded choresCESearch k`.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e…), pp.3–4 (CLS membership cited from Chaudhury–Garg–McGlaughlin–Mehta 2022); equilibrium conditions in Definitions 2.1–2.2, p.6.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash

/-- Exact rational competitive equilibria of valid rational linear chores markets, together with
the prescribed answer-length bound, are polynomial-time verifiable on Cook's machines. -/
theorem LinearChoresCLS.chores_ce_checkable (k : ℕ) :
    CookPvsNP.checkLang (fun x y => (bounded choresCESearch k).valid x ∧
      (bounded choresCESearch k).answer x y) ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) := by sorry
