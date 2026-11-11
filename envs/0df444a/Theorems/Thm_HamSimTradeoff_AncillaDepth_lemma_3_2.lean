-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_lemma_3_2
-- name    : HamSimTradeoff.AncillaDepth.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:01.892357+00:00
-- url     : https://prove2.me/theorems/9b0f679b-8215-40ab-8685-0871e32b222c
-- title:
--   Lemma 3.2 — uniform lower bound for Suzuki coefficients
-- statement:
--   There is an absolute constant $C>0$ such that for all integers $n\ge k\ge1$,
--   $$(2n+1)!\,|c_{k,n}|\ge\exp\bigl(-C(kn+k\log k)\bigr).$$
--   Here $c_{k,n}$ are the explicit Suzuki response coefficients and $\log$ is the natural logarithm. This quantitative nonvanishing estimate is uniform in both order and coefficient index.
--
--   **Formalization Note** The paper writes $e^{-O(\cdot)}$; the Lean states an absolute constant $C$ chosen before all parameters. The proof invokes an unspecified absolute constant, so no numerical value is asserted.
--
--   Differences from the source:
--   - encoding: O(·) or exp(−O(·)) with an absolute hidden constant → a positive real constant chosen before all other parameters; reason: the proof supplies no numeral; quantifier order enforces uniformity
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), p.16, Lemma 3.2

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- The constant precedes n and k; no instance-dependent big-O witness. -/
theorem lemma_3_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      Real.exp (-C * ((k : ℝ) * n + (k : ℝ) * Real.log k)) ≤
        (Nat.factorial (2 * n + 1) : ℝ) * |coefficient k n| := by sorry

end HamSimTradeoff.AncillaDepth
