-- Prove2me | Theorems.Thm_FriedmannCunningham_parity_lower_bound
-- name    : FriedmannCunningham.parity_lower_bound
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-02T05:11:28.662095+00:00
-- url     : https://prove2.me/theorems/a6b402d1-47d5-47f4-a2ac-8c5a09ad8c2c
-- title:
--   Theorem 4 — parity-game lower bound
-- statement:
--   For every n≥3 the explicit parity game admits a complete strategy-improvement run from the prescribed initial strategy, with the prescribed cyclic edge order, using at least 2^n switches.
-- source:
--   Avis and Friedmann (2017), Theorem 4, §2.4. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 4, with the explicit Figure 2 graph and multiplicity valuations. -/
theorem parity_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → ParityState n), parityRun n hn s T ∧ 2 ^ n ≤ T := by sorry

end FriedmannCunningham
