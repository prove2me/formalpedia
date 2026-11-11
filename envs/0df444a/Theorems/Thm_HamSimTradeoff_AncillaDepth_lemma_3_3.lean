-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_lemma_3_3
-- name    : HamSimTradeoff.AncillaDepth.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:57.852744+00:00
-- url     : https://prove2.me/theorems/0b36076d-86b5-4b5a-b7ac-bb43ca8223aa
-- title:
--   Lemma 3.3 — a controller moment has a uniform lower bound
-- statement:
--   There is an absolute constant $C>0$ such that every architecture, with order $2k$, rounds $s$, branch count $R=2^a$, ideal amplitude $\eta$, and normalized depth $Q$, has one integer $n\in\{k,\ldots,k+sR-1\}$ satisfying both
--   $$|M_n|\ge\frac{|\eta|}{sRQ^{2k}(2Q^4)^{sR-1}},\qquad |M_n|\ge|\eta|\exp\bigl(-C(k+sR)\log(sRQ)\bigr).$$
--   The same moment witnesses both conclusions. This estimate concerns only refinement integers and controller matrices, with no Hamiltonian or accuracy assumption. It includes $\eta=0$ and the one-branch case $s=R=Q=1$.
--
--   **Formalization Note** The paper writes $e^{-O(\cdot)}$; the Lean states an absolute constant $C$ chosen before all parameters. The index range uses $k\le n<k+sR$, equivalent to the printed inclusive upper endpoint.
--
--   Differences from the source:
--   - encoding: O(·) or exp(−O(·)) with an absolute hidden constant → a positive real constant chosen before all other parameters; reason: the proof supplies no numeral; quantifier order enforces uniformity
--   - reading: Q = D/L = Θ(5^{k−1}∑ℓ max_r mℓr) → Q = 5^{k−1}∑ℓ max_r mℓr exactly; reason: this is the displayed representative used by the proof, preserving the asymptotic resource scale
--   - encoding: indices 1,…,L, rounds 1,…,s and branches 1,…,R → zero-based Fin indices, with ancilla |0^a⟩ represented by index zero; reason: a bijective relabeling preserves every matrix product and sum
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), p.16, Lemma 3.3; proof p.17

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- Both bounds have the same witness n; Q is the exact normalized depth expression. -/
theorem lemma_3_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Architecture, ∃ n : ℕ,
      B.k ≤ n ∧ n < B.k + B.s * 2 ^ B.a ∧
      ‖eta B‖ / ((B.s * 2 ^ B.a : ℕ) * depth B ^ (2 * B.k) *
        (2 * depth B ^ 4) ^ (B.s * 2 ^ B.a - 1)) ≤ ‖moment B n‖ ∧
      ‖eta B‖ * Real.exp (-C * (((B.k : ℝ) + (B.s * 2 ^ B.a : ℕ)) *
        Real.log ((B.s * 2 ^ B.a : ℕ) * depth B))) ≤ ‖moment B n‖ := by sorry

end HamSimTradeoff.AncillaDepth
