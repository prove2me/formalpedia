-- Prove2me | Theorems.Thm_OnlinePrimalDual_BoundedAllocation_lemma13_2
-- name    : OnlinePrimalDual.BoundedAllocation.lemma13_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:06:39.814235+00:00
-- url     : https://prove2.me/theorems/70b32a1d-ce83-453a-92a7-c4dd4fa168f6
-- title:
--   Lemma 13.2 — matching lower bound on C(d)
-- statement:
--   Let k be the largest value (0 ≤ k ≤ d) for which H(d) - H(d-k) ≤ 1. Then
--   C(d) ≤ 1 - (k - k·H(d) + Σ_{i=1}^k H(d-i))/d.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 244, Lemma 13.2

import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_competitiveRatio
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_harmonicNum

namespace OnlinePrimalDual.BoundedAllocation

/-- **Lemma 13.2** (p. 244, PDF p. 155) — the matching lower bound. `k` is "the largest value for
which `H(d) - H(d-k) ≤ 1`": formalized via `hk_bound` (`k` satisfies the inequality) together
with `hk_largest` (maximality: every `k' > k` violates it), rather than merely `∃ k, …`, so that
`k` is pinned to the specific value the book's proof needs (`reference/FAITHFULNESS_TRAPS.md`
trap 9, quantifier precision for an extremal value). -/
theorem lemma13_2 (d k : ℕ) (hd : 2 ≤ d) (hk_le : k ≤ d)
    (hk_bound : harmonicNum d - harmonicNum (d - k) ≤ 1)
    (hk_largest : ∀ k', k < k' → k' ≤ d → 1 < harmonicNum d - harmonicNum (d - k')) :
    competitiveRatio d ≤
      1 - ((k : ℝ) - (k : ℝ) * harmonicNum d + ∑ i ∈ Finset.Icc 1 k, harmonicNum (d - i)) /
        (d : ℝ) := by sorry

end OnlinePrimalDual.BoundedAllocation
