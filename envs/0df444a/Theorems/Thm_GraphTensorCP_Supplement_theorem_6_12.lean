-- Prove2me | Theorems.Thm_GraphTensorCP_Supplement_theorem_6_12
-- name    : GraphTensorCP.Supplement.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:27:02.984238+00:00
-- url     : https://prove2.me/theorems/271c819a-04b4-4919-8f8f-9df6f2f56891
-- title:
--   Theorem 6.12 — complete split graphs
-- statement:
--   Let $\mathbb F$ be any field and let $a,b$ be positive integers. If $b\ge a$, then
--
--   $$
--   \Gamma_{\mathbb F}(J_{a,b})=U^\Delta_{\mathrm{CP}}(J_{a,b})
--   =U_{\mathrm{CP}}(J_{a,b})=ab=\mathrm{MaxCut}(J_{a,b}).
--   $$
--
--   If $b<a$, then
--
--   $$
--   \left\lfloor\frac{(a+b)^2}{4}\right\rfloor
--   \le\Gamma_{\mathbb F}(J_{a,b})\le\frac{(a+b)^2}{4}.
--   $$
--
--   These bounds coincide when $a+b$ is even. More generally, every split graph with a specified clique part of size $a$ and independent part of size $b$ obeys the corresponding upper bound: $ab$ when $a\le b$, and $(a+b)^2/4$ otherwise.
--
--   Differences from the source:
--   - encoding: the source specifies an abstract clique/independent partition → Lean labels the clique by the first $a$ elements of `Fin (a+b)` and the independent set by the final $b$ elements; reason: this fixes a representative of the same partitioned graph, while the general split-graph clause quantifies over every graph with that specified partition.
--   - encoding: the source writes the floor of $(a+b)^2/4$ → Lean performs natural-number division before coercing the result to $\mathbb R$; reason: for a nonnegative integer numerator this is exactly the floor.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 6.12, pp.64–65

import Mathlib
import Definitions.Def_GraphTensorCP_maxCut
import Definitions.Def_GraphTensorCP_uCPDelta
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_GraphTensorCP_Supplement_uCP
import Definitions.Def_GraphTensorCP_Supplement_completeSplitGraph

universe u

namespace GraphTensorCP

namespace Supplement

/-- **Theorem 6.12 (complete split graphs)**, Zhou, *Asymptotic Rank of Weighted Graph Tensors
via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), pp.64–65.
Both regimes, parity exactness, and the upper bound for every split graph with the specified
partition are included.

**Formalization Note.** `completeSplitGraph a b` labels the clique first and the independent set
second. The floor is natural-number division before coercion to `ℝ`. The final universally
quantified `G` may omit arbitrary cross edges while retaining the specified clique/independent
partition. -/
theorem theorem_6_12 {K : Type u} [Field K] (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (G : SimpleGraph (Fin (a + b))) [DecidableRel G.Adj] (hG : IsSplitWithParts G) :
    let J := completeSplitGraph a b
    (b ≥ a →
      gammaF K (by omega) (J.adjMatrix ℝ) = uCPDelta (J.adjMatrix ℝ) ∧
      uCPDelta (J.adjMatrix ℝ) = uCP (J.adjMatrix ℝ) ∧
      uCP (J.adjMatrix ℝ) = (a : ℝ) * b ∧
      (a : ℝ) * b = maxCut (J.adjMatrix ℝ)) ∧
    (b < a →
      (((a + b) ^ 2 / 4 : ℕ) : ℝ) ≤ gammaF K (by omega) (J.adjMatrix ℝ) ∧
      gammaF K (by omega) (J.adjMatrix ℝ) ≤ ((a + b : ℕ) : ℝ) ^ 2 / 4) ∧
    (b < a → Even (a + b) →
      gammaF K (by omega) (J.adjMatrix ℝ) = ((a + b : ℕ) : ℝ) ^ 2 / 4) ∧
    gammaF K (by omega) (G.adjMatrix ℝ) ≤
      if a ≤ b then (a : ℝ) * b else ((a + b : ℕ) : ℝ) ^ 2 / 4 := by sorry

end Supplement

end GraphTensorCP
