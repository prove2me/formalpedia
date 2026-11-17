-- Prove2me | Theorems.Thm_GraphTensorCP_Supplement_theorem_6_14
-- name    : GraphTensorCP.Supplement.theorem_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:27:34.257106+00:00
-- url     : https://prove2.me/theorems/3eaa81e7-ed1c-48f8-b371-5a28ddfa6705
-- title:
--   Theorem 6.14 — wheel bounds
-- statement:
--   Let $\mathbb F$ be any field. For every $m\ge3$, the wheel with $m$ rim vertices satisfies
--
--   $$
--   \left\lfloor\frac{3m}{2}\right\rfloor\le\Gamma_{\mathbb F}(W_m)
--   \le U^\Delta_{\mathrm{CP}}(W_m)=U^\Delta_{\mathrm{SDP}}(W_m)
--   =\begin{cases}
--   25m/16,&m\text{ even},\\
--   (5m+1)^2/(16(m+1)),&m\text{ odd}.
--   \end{cases}
--   $$
--
--   When $m$ is even, the same value $25m/16$ also equals the unstrengthened value $U_{\mathrm{CP}}(W_m)$.
--
--   **Formalization Note** The published `SparseDisc.wheel m` uses `Option (Fin m)` for the named wheel. Lean states the tensor bound for an arbitrary isomorphic representative on `Fin (m+1)`, the vertex type expected by the published graph-tensor exponent.
--
--   Differences from the source:
--   - encoding: the source names the wheel $W_m$ without fixing a vertex type → Lean reuses the published `SparseDisc.wheel m` and quantifies over an isomorphic representative on `Fin (m+1)`; reason: graph isomorphism only relabels the same wheel and keeps $m$ as the number of rim vertices.
--   - encoding: the source writes $\lfloor3m/2\rfloor$ → Lean performs natural-number division before coercion to $\mathbb R$; reason: this is the same floor for $m\ge0$.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 6.14, pp.65–67

import Mathlib
import Definitions.Def_GraphTensorCP_maxCut
import Definitions.Def_GraphTensorCP_uCPDelta
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_GraphTensorCP_Supplement_uCP
import Definitions.Def_GraphTensorCP_Supplement_uSDPDelta
import Definitions.Def_SparseDisc_wheel

universe u

namespace GraphTensorCP

namespace Supplement

/-- **Theorem 6.14 (wheel bounds)**, Zhou, *Asymptotic Rank of Weighted Graph Tensors via
Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), pp.65–67.
The statement retains the maximum-cut lower bound, both parity branches of the exact strengthened
values, and the extra equality with unstrengthened `U_CP` for even rims.

**Formalization Note.** The published `SparseDisc.wheel m` has vertex type `Option (Fin m)`.
The theorem is stated for an arbitrary isomorphic representative `G` on `Fin (m+1)`, the vertex
type required by the published graph-tensor exponent; hence `m` remains the number of rim vertices.
The floor in `⌊3m/2⌋` is natural-number division before coercion to `ℝ`. -/
theorem theorem_6_14 {K : Type u} [Field K] (m : ℕ) (hm : 3 ≤ m)
    (G : SimpleGraph (Fin (m + 1))) [DecidableRel G.Adj]
    (hG : Nonempty (G ≃g SparseDisc.wheel m)) :
    (((3 * m) / 2 : ℕ) : ℝ) ≤ gammaF K (by omega) (G.adjMatrix ℝ) ∧
    gammaF K (by omega) (G.adjMatrix ℝ) ≤ uCPDelta (G.adjMatrix ℝ) ∧
    uCPDelta (G.adjMatrix ℝ) = uSDPDelta (G.adjMatrix ℝ) ∧
    (Even m →
      uCPDelta (G.adjMatrix ℝ) = 25 * (m : ℝ) / 16 ∧
      uCP (G.adjMatrix ℝ) = 25 * (m : ℝ) / 16) ∧
    (Odd m →
      uCPDelta (G.adjMatrix ℝ) = (5 * (m : ℝ) + 1) ^ 2 / (16 * (m + 1))) := by sorry

end Supplement

end GraphTensorCP
