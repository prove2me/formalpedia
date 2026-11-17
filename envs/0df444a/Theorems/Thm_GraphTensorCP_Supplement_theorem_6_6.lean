-- Prove2me | Theorems.Thm_GraphTensorCP_Supplement_theorem_6_6
-- name    : GraphTensorCP.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:25:54.7014+00:00
-- url     : https://prove2.me/theorems/72826f7b-e1e1-49b0-a5da-704144b65bd0
-- title:
--   Theorem 6.6 — odd-cycle bound
-- statement:
--   Let $\mathbb F$ be any field. For every odd integer $m\ge3$, the cycle $C_m$ satisfies
--
--   $$
--   m-1\le\Gamma_{\mathbb F}(C_m)\le U^\Delta_{\mathrm{CP}}(C_m)
--   =U^\Delta_{\mathrm{SDP}}(C_m)=\frac{m^2}{m+1}
--   =m-1+\frac1{m+1}.
--   $$
--
--   Thus the strengthened copositive and semidefinite programs have the same exact value on every odd cycle and leave only a $1/(m+1)$ gap above the maximum-cut lower bound.
--
--   Differences from the source:
--   - encoding: the source labels the cycle vertices $1,\ldots,m$ → Lean uses Mathlib’s `cycleGraph m` on `Fin m`; reason: this is the same cycle after shifting the vertex labels by one.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 6.6, pp.59–60

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Definitions.Def_GraphTensorCP_uCPDelta
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_GraphTensorCP_Supplement_uSDPDelta

universe u

namespace GraphTensorCP

namespace Supplement

/-- **Theorem 6.6 (odd-cycle bound)**, Zhou, *Asymptotic Rank of Weighted Graph Tensors via
Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), pp.59–60.

**Formalization Note.** `SimpleGraph.cycleGraph m` is the cycle on the 0-based vertex type
`Fin m`; graph parameters are evaluated on its real adjacency matrix. The hypotheses retain both
the lower threshold `m ≥ 3` and oddness. -/
theorem theorem_6_6 {K : Type u} [Field K] (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    (m : ℝ) - 1 ≤ gammaF K (by omega) ((SimpleGraph.cycleGraph m).adjMatrix ℝ) ∧
    gammaF K (by omega) ((SimpleGraph.cycleGraph m).adjMatrix ℝ) ≤
      uCPDelta ((SimpleGraph.cycleGraph m).adjMatrix ℝ) ∧
    uCPDelta ((SimpleGraph.cycleGraph m).adjMatrix ℝ) =
      uSDPDelta ((SimpleGraph.cycleGraph m).adjMatrix ℝ) ∧
    uSDPDelta ((SimpleGraph.cycleGraph m).adjMatrix ℝ) = (m : ℝ) ^ 2 / (m + 1) ∧
    (m : ℝ) ^ 2 / (m + 1) = (m : ℝ) - 1 + 1 / (m + 1) := by sorry

end Supplement

end GraphTensorCP
