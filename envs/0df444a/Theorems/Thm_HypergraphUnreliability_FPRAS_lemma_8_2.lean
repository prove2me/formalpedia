-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_8_2
-- name    : HypergraphUnreliability.FPRAS.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:40.369624+00:00
-- url     : https://prove2.me/theorems/380939be-b806-446b-87dd-6c8251b5847b
-- title:
--   Lemma 8.2 — Worst-case running time and random-bit usage
-- statement:
--   The algorithm of §§7–8 has bounded polynomial running time and random-bit usage in the parameters of Theorem 1.2. There are one fair-bit machine and one polynomial $P$, chosen before all inputs, with the following property. Let $s$ be the sum of the explicit input length, $\lceil\varepsilon^{-1}\rceil$ and $1+\lceil\log_2(1/\delta)\rceil$. On every valid input and every tape of more than $P(s)$ bits, the machine halts within $P(s)$ steps, uses at most $P(s)$ tape bits, and outputs the value of the algorithm on that tape. In the sampling case the algorithm's fixed bit budget is at most $P(s)$.
--
--   The bound holds for every random outcome, not in expectation. The procedure covered is the whole of §§7–8, including batching and the output arithmetic.
--
--   Differences from the source:
--   - encoding: polynomial time in the bit model → one fixed Mathlib `Turing.FinTM2` with finite alphabets and one fixed polynomial bounding its steps, chosen before the inputs; reason: a `FinTM2` step executes a bounded program fragment on a finite alphabet, so steps and bit operations agree up to a constant factor; every instance of the claim is kept
--   - encoding: random bits read on demand → a tape longer than the bound, in a dedicated stack, the machine required to work for every such length; reason: a machine reading at most $B$ bits cannot observe the end of the tape, and the tape length carries no advice
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 8.2, p. 11; Theorem 1.2, p. 2; (8.2), p. 11

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_CommonAlgorithm

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 8.2, p. 11: one fair-bit machine and one polynomial, chosen before the inputs, such that on
every valid input of Theorem 1.2 (of resource size `s`, the explicit input length plus `⌈ε⁻¹⌉` plus
`1 + ⌈log₂(1/δ)⌉`) and every tape of more than `P(s)` bits, the machine halts within `P(s)` steps, uses
at most `P(s)` tape bits, and outputs the value of the §§7–8 algorithm on that tape. In the sampling
case the algorithm's fixed bit budget is at most `P(s)`. -/
theorem lemma_8_2 :
    ∃ (M : CoinMachine) (P : Polynomial ℕ), ∀ x : CommonInstance, x.Valid →
      (x.IsSamplingCase → x.params.totalBits ≤ P.eval x.resourceSize) ∧
      ∀ (T : ℕ), P.eval x.resourceSize < T → ∀ ω : Fin T → Bool,
        ∃ û : Frac, 0 < û.den ∧ û.val = x.output (tapeBit ω) ∧
          M.RunsWithin x.encode (tapeList ω) (P.eval x.resourceSize) (fracCode û) := by sorry

end HypergraphUnreliability.FPRAS
