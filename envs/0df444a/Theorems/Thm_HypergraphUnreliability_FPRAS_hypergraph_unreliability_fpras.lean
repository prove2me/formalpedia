-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_hypergraph_unreliability_fpras
-- name    : HypergraphUnreliability.FPRAS.hypergraph_unreliability_fpras
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:45.804244+00:00
-- url     : https://prove2.me/theorems/925fec0d-a0c4-41e2-b580-c4e5290f395e
-- title:
--   Theorem 1.1 — an FPRAS for hypergraph unreliability with independent rational edge failures
-- statement:
--   Given an explicitly represented undirected hypergraph $H$, independent rational edge-failure probabilities $p_e\in[0,1]$, and rational $\varepsilon,\delta\in(0,1)$, there is a randomized algorithm returning a rational $\hat u\in[0,1]$ such that
--   $$P\bigl[|\hat u-u_H(p)|\le\varepsilon u_H(p)\bigr]\ge1-\delta .$$
--   For every random outcome, its running time and random-bit usage are polynomial in the explicit input length, all probability encoding lengths, $\varepsilon^{-1}$ and $\log(1/\delta)$. The rank is unrestricted.
--
--   Precisely: one fair-bit machine and one polynomial $P$ are chosen before all inputs. With $s$ the sum of the total encoding length, $\lceil\varepsilon^{-1}\rceil$ and $1+\lceil\log_2(1/\delta)\rceil$, on every valid input and every tape of more than $P(s)$ fair bits the machine halts within $P(s)$ steps, uses at most $P(s)$ tape bits, and returns a written rational in $[0,1]$, and the displayed bound holds under the fair bits.
--
--   All boundary cases are included: $n\le1$, disconnected inputs, and probabilities $0$ and $1$. No connectivity, rank, simplicity or common-probability hypothesis is assumed.
--
--   Differences from the source:
--   - encoding: polynomial time in the bit model → one fixed Mathlib `Turing.FinTM2` with finite alphabets and one fixed polynomial bounding its steps, chosen before the inputs; reason: a `FinTM2` step executes a bounded program fragment on a finite alphabet, so steps and bit operations agree up to a constant factor; every instance of the claim is kept
--   - encoding: the randomized algorithm draws fair bits → a tape longer than the bound, in a dedicated stack, the machine required to work for every such length; reason: a machine reading at most $B$ bits cannot observe the end of the tape, and the tape length carries no advice
--   - encoding: vertices labeled by $[n]$ → `Fin n`, labels $0,\dots,n-1$; reason: a bijective relabeling
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Theorem 1.1, p. 2

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Instance

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- **Theorem 1.1**, p. 2. There are one fair-bit machine and one polynomial `P`, chosen before all
inputs, such that on every explicitly represented undirected hypergraph with rational failure
probabilities `p_e ∈ [0,1]` and rational `ε, δ ∈ (0,1)`, with resource size `s` (the total encoding
length, `⌈ε⁻¹⌉` and `1 + ⌈log₂(1/δ)⌉`), and for every tape of more than `P(s)` fair bits:
for every random outcome the machine halts within `P(s)` steps, uses at most `P(s)` tape bits, and
returns a written rational `û ∈ [0,1]`; and `P[|û - u_H(p)| ≤ ε u_H(p)] ≥ 1 - δ`. The rank is
unrestricted. -/
theorem hypergraph_unreliability_fpras :
    ∃ (M : CoinMachine) (P : Polynomial ℕ), ∀ x : RawInstance, x.Valid →
      ∀ T : ℕ, P.eval x.resourceSize < T →
        (∀ ω : Fin T → Bool, ∃ û : Frac, 0 < û.den ∧ 0 ≤ û.val ∧ û.val ≤ 1 ∧
          M.RunsWithin x.encode (tapeList ω) (P.eval x.resourceSize) (fracCode û)) ∧
        1 - ((x.δ.val : ℚ) : ℝ) ≤ fairProb T (fun ω =>
          ∃ û : Frac, 0 < û.den ∧
            M.RunsWithin x.encode (tapeList ω) (P.eval x.resourceSize) (fracCode û) ∧
            |((û.val : ℚ) : ℝ) - x.target| ≤ ((x.ε.val : ℚ) : ℝ) * x.target) := by sorry

end HypergraphUnreliability.FPRAS
