-- Prove2me | Theorems.Thm_GraphTensorCP_Supplement_theorem_B_5
-- name    : GraphTensorCP.Supplement.theorem_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:28:06.811845+00:00
-- url     : https://prove2.me/theorems/2e3be5a7-c5b0-4a66-920a-24eb5d38c2b8
-- title:
--   Theorem B.5 — weighted minimum-cut equality for asymptotic subrank
-- statement:
--   Let $\mathbb F$ be any field, let $n\ge2$, and let $Q$ be any dimension matrix with logarithmic edge-weight matrix $W$. Then
--
--   $$
--   \log_2\widetilde Q_{\mathbb F}(\mathsf{WT}(Q))=\mathrm{MinCut}(W).
--   $$
--
--   The equality includes disconnected support graphs, zero edge weights, and edges of dimension one. It identifies weighted minimum cut exactly—not only up to constants—with the asymptotic subrank of the weighted graph tensor.
--
--   **Formalization Note** The tensor parameter is the locally defined standard asymptotic subrank, not asymptotic rank. `IsDimMatrix` allows entries equal to one, and `minCut` ranges over every nonempty proper subset of `Fin n`.
--
--   Differences from the source:
--   - encoding: the source’s asymptotic subrank is written as a limit → Lean uses the equivalent supremum over positive Kronecker powers and defines it locally because the published MME rank module has no subrank declaration; reason: Definitions 2.12–2.13 give this parameter and prove the supremum formula, with the zeroth power excluded.
--   - encoding: the source uses mixed-radix coordinates for $\mathsf{WT}(Q)$ → Lean uses the published product-coordinate `wt`; reason: the two tensors differ only by coordinate permutations within their legs.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem B.5, p.80

import Mathlib
import Definitions.Def_GraphTensorCP_IsDimMatrix
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_GraphTensorCP_Supplement_minCut
import Definitions.Def_GraphTensorCP_Supplement_tensorAsymptoticSubrank

universe u

namespace GraphTensorCP

namespace Supplement

/-- **Theorem B.5 (weighted minimum-cut equality)**, Zhou, *Asymptotic Rank of Weighted Graph
Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.80.
For every field and every dimension matrix of order at least two, the base-two logarithm of the
asymptotic subrank of its weighted graph tensor equals the minimum cut of the logarithmic weights.

**Formalization Note.** This is asymptotic **subrank**, not rank. `minCut` ranges over nonempty
proper subsets of `Fin n`. Dimension-one edges and disconnected support remain allowed because
`IsDimMatrix` only requires entries at least one. -/
theorem theorem_B_5 {K : Type u} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℕ) (hQ : IsDimMatrix Q) :
    Real.logb 2 (tensorAsymptoticSubrank hn (wt K Q)) = minCut (logWeight Q) := by sorry

end Supplement

end GraphTensorCP
