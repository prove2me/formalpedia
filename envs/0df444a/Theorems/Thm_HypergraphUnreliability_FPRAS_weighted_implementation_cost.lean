-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_weighted_implementation_cost
-- name    : HypergraphUnreliability.FPRAS.weighted_implementation_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:35.222097+00:00
-- url     : https://prove2.me/theorems/141b6e43-e3de-425a-99f1-b08719e00c9e
-- title:
--   Proof of Theorem 1.1 — running time and random bits of the algorithm of §§9.1–9.5
-- statement:
--   There are one fair-bit machine and one polynomial $P$, chosen before all inputs, with the following property. Let $s$ be the resource size of Theorem 1.1. On every valid input and every tape of more than $P(s)$ bits, the machine halts within $P(s)$ steps, uses at most $P(s)$ tape bits, and outputs the value of the algorithm of §§9.1–9.5 on that tape. In the sampling case its fixed bit budget is at most $P(s)$.
--
--   This is the resource half of Theorem 1.1, stated for the concrete procedure. Lemma 9.2, (9.3), Lemma 9.3 and the scans of Lemma 8.2 enter here.
--
--   Differences from the source:
--   - encoding: polynomial time in the bit model → one fixed Mathlib `Turing.FinTM2` with finite alphabets and one fixed polynomial bounding its steps, chosen before the inputs; reason: a `FinTM2` step executes a bounded program fragment on a finite alphabet, so steps and bit operations agree up to a constant factor; every instance of the claim is kept
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Proof of Theorem 1.1, last paragraph, p. 16

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_WeightedAlgorithm

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- The cost of the algorithm of §§9.1–9.5 (proof of Theorem 1.1, last paragraph, p. 16): one fair-bit
machine and one polynomial, chosen before the inputs, such that on every valid input and every tape of
more than `P(s)` bits the machine halts within `P(s)` steps, uses at most `P(s)` tape bits, and outputs
the value of the algorithm on that tape. In the sampling case the fixed bit budget is at most `P(s)`. -/
theorem weighted_implementation_cost :
    ∃ (M : CoinMachine) (P : Polynomial ℕ), ∀ x : RawInstance, x.Valid →
      (x.IsSamplingCase → x.totalBits ≤ P.eval x.resourceSize) ∧
      ∀ (T : ℕ), P.eval x.resourceSize < T → ∀ ω : Fin T → Bool,
        ∃ û : Frac, 0 < û.den ∧ û.val = x.output (tapeBit ω) ∧
          M.RunsWithin x.encode (tapeList ω) (P.eval x.resourceSize) (fracCode û) := by sorry

end HypergraphUnreliability.FPRAS
