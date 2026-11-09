-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_weighted_output_guarantee
-- name    : HypergraphUnreliability.FPRAS.weighted_output_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:27.39247+00:00
-- url     : https://prove2.me/theorems/6750cb93-1ef9-45f4-a2b6-3ca8c1cb7dcb
-- title:
--   Proof of Theorem 1.1 — the guarantee of the algorithm of §§9.1–9.5
-- statement:
--   On every valid explicit input, the algorithm of §§9.1–9.5 returns a rational $\hat u\in[0,1]$ on every bit stream, and, for every tape length at least its bit budget,
--   $$P\bigl[|\hat u-u_H(p)|\le\varepsilon u_H(p)\bigr]\ge1-\delta .$$
--
--   This is the correctness half of Theorem 1.1, stated for the concrete procedure. It combines preprocessing, (9.4), (9.11) and (9.12) through the factorization of the output on p. 15.
--
--   Differences from the source: none.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Proof of Theorem 1.1, pp. 15–16; (9.11), p. 15

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_WeightedAlgorithm

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- The approximation guarantee of the algorithm of §§9.1–9.5 (proof of Theorem 1.1, pp. 15–16): on every
valid input, the output is a rational in `[0, 1]` on every bit stream, and, under fair bits,
`|û - u_H(p)| ≤ ε u_H(p)` with probability at least `1 - δ`. -/
theorem weighted_output_guarantee (x : RawInstance) (hx : x.Valid) (T : ℕ) (hT : x.totalBits ≤ T) :
    (∀ ω : ℕ → Bool, 0 ≤ x.output ω ∧ x.output ω ≤ 1) ∧
    1 - ((x.δ.val : ℚ) : ℝ) ≤ fairProb T (fun ω =>
      |((x.output (tapeBit ω) : ℚ) : ℝ) - x.target| ≤ ((x.ε.val : ℚ) : ℝ) * x.target) := by sorry

end HypergraphUnreliability.FPRAS
