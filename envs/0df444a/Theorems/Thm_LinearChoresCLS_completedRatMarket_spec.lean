-- Prove2me | Theorems.Thm_LinearChoresCLS_completedRatMarket_spec
-- name    : LinearChoresCLS.completedRatMarket_spec
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:28.412728+00:00
-- url     : https://prove2.me/theorems/fa36d6e2-e5ad-4386-8650-5bf4349cbeca
-- title:
--   The canonical rational market has the specified completed-market data
-- statement:
--   The canonical `Fin`-indexed rational market from Section 7.1 agrees entrywise with the completed market $f(I)$ after transporting its named agents and chores. In particular, basic chore $j$ is at index $j$, so the decoder (7.3) reads the intended columns. This proves the data-correctness half of the serialization assertion on p.32.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Section 7.1 (i)–(iv), p.31, and price mapping (7.3), p.32.

import Definitions.Def_LinearChoresCLS_EncodedMarket

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- The public rational market has precisely the data and basic-chore positions of
Section 7.1. -/
theorem completedRatMarket_spec {n : ℕ} (P : Quadratic n) (ε : ℚ) :
    (∀ j : Fin (n + 1),
      (choreFinEquiv n (chainLength P ε) (Sum.inl j)).val = j.val) ∧
    (∀ i j, ((completedRatMarket P ε).disutil
      (agentFinEquiv n (chainLength P ε) i) (choreFinEquiv n (chainLength P ε) j) : ℝ) =
      (completedMarket P ε).disutil i j) ∧
    (∀ i, ((completedRatMarket P ε).earn (agentFinEquiv n (chainLength P ε) i) : ℝ) =
      (completedMarket P ε).earn i) ∧
    (∀ j, ((completedRatMarket P ε).supply (choreFinEquiv n (chainLength P ε) j) : ℝ) =
      (completedMarket P ε).supply j) := by sorry
