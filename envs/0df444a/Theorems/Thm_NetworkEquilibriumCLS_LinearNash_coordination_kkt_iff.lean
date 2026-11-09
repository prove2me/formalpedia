-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_coordination_kkt_iff
-- name    : NetworkEquilibriumCLS.LinearNash.coordination_kkt_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:01.309667+00:00
-- url     : https://prove2.me/theorems/c8903d72-9bad-4b3a-b14d-fbe1c1ef8126
-- title:
--   Lemma 2.4 — exact coordination Nash if and only if potential KKT
-- statement:
--   Let G be a binary-action common-payoff network coordination game with arbitrary rational 2×2 edge matrices (the [0,1] bound of the search problem in §1.1 is not needed here), and let x be any real vector in [0,1]^N. Write Φ_G for the sum of the expected common edge payoffs, counting each edge once. Then
--
--   $$x\text{ is Nash for }G\quad\Longleftrightarrow\quad x\text{ is box KKT for minimizing }-\Phi_G.$$
--
--   Nash uses every player and both pure deviations under independent mixing. KKT uses genuine coordinate derivatives, with nonnegative derivative at zero and nonpositive derivative at one. Both directions and the whole real cube are retained. This is the analytic bridge from potential optimization to the game.
--
--   Differences from the source:
--   - encoding: positive dimensions and indices 1 through d → Fin d with d positive and indices 0 through d-1; reason: a bijective relabelling; all real-cube coordinates and all boundary cases are retained
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.7 (PDF 8), Lemma 2.4.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Games

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem coordination_kkt_iff :
    ∀ (N : ℕ), 0 < N → ∀ (G : Coordination N),
    ∀ x : Fin N → ℝ, InCube x →
      (CoordinationNash G x ↔ FunctionKKT (fun z => -coordinationPotential G z) x) := by sorry

end NetworkEquilibriumCLS.LinearNash
