-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_independent_coefficient_batch_mqpt
-- name    : InfoLossLAR.WorstCase.RegevSearch.independent_coefficient_batch_mqpt
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T13:40:34.241839+00:00
-- url     : https://prove2.me/theorems/1817c57c-2cbe-4815-9665-53e3775d3d76
-- title:
--   Independent circuit repetitions with a decoded coefficient pool
-- statement:
--   Let $H$ be a uniform quantum polynomial-time multi-output circuit family. There is a single such family $G$ that batches independent executions on inputs specifying an integer matrix $B$, rational parameter $r$, output count $m$, and numerical budget $b$. Both $m$ and $b$ are encoded in unary.
--
--   Let $p(z)$ be the probability that one copy of $H$, run at count one and precision $m(b+1)$, outputs a word beginning with the encoding of the integer vector $z$. Whenever these probabilities sum to one, the output of $G$ has the exact joint law
--
--   $$
--   \Pr[G(B,r,m,b)\text{ encodes a pool in }E]
--   =\sum_{(z_1,\ldots,z_m)\in E}\prod_{i=1}^{m}p(z_i)
--   $$
--
--   for every event $E$ on the decoded pool. This includes the unique empty pool at $m=0$. The uniform circuit construction must arrange independent workspaces, form the one-copy inputs, and pack the measured coefficient vectors in the public output format. The result applies to any normalized coefficient readout law.
-- source:
--   John Watrous, The Theory of Quantum Information, https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf, §2.3, p. 105, product measurements on compound registers, Eqs. (2.216)–(2.219). The exact law is the product measurement law for disjoint runs on a fixed classical input. Uniform repetition, the unary precision calculation and the coefficient pool encoding are the platform-specific circuit construction.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem independent_coefficient_batch_mqpt (H : MFamily) (hH : IsMQPT H) :
    ∃ G : MFamily, IsMQPT G ∧
      ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (count budget : ℕ),
        let precision := count * (budget + 1)
        let draw (z : Fin n → ℤ) := outputProb H (dgsInput B r 1 precision)
          (fun out => encVec encI z <+: out)
        HasSum draw 1 → ∀ event : (Fin count → Fin n → ℤ) → Prop,
          outputProb G (dgsInput B r count budget) (decodedPoolEvent event) =
            ∑' pool : Fin count → Fin n → ℤ,
              (∏ i, draw (pool i)) * (if event pool then 1 else 0) := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
