-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_theorem_7
-- name    : MultiItemRev.KBundling.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:48.101207+00:00
-- url     : https://prove2.me/theorems/fe0fdb57-2c4d-4439-8810-55cb42f6a034
-- title:
--   Theorem 7, p. 18 — for independent Y, Z: Rev(Y,Z) ≤ Rev(Y)+Rev(Z)+BRev(Y)+BRev(Z) ≤ 2(Rev(Y)+Rev(Z))
-- statement:
--   **Theorem 7 (decomposition).** Let $Y$ and $Z$ be multi-dimensional nonnegative random variables (with at least one coordinate each). If $Y$ and $Z$ are independent, then
--   $$\mathrm{Rev}(Y,Z)\le\mathrm{Rev}(Y)+\mathrm{Rev}(Z)+\mathrm{BRev}(Y)+\mathrm{BRev}(Z)\qquad(6)$$
--   $$\le 2\,(\mathrm{Rev}(Y)+\mathrm{Rev}(Z)).\qquad(7)$$
--
--   The optimal revenue from two independent groups of goods is controlled by the revenues of the groups and of their bundles. Applied inductively to halves of $2^m$ i.i.d. goods, it gives $R_k\le2B_{k/2}+4B_{k/4}+\dots+kB_1+kR_1$ in the proof of Theorem D.
--
--   **Formalization Note** $Y$ and $Z$ have laws $\mu_Y,\mu_Z$ on `ι₁ → ℝ≥0` and `ι₂ → ℝ≥0` with nonempty finite `ι₁, ι₂` ($k_1,k_2\ge1$, p. 18); the law of $(Y,Z)$ is their product (`jointLaw`). This is the goal theorem of mission 1 of this series, restated here with the same statement.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 18, Theorem 7, (6) and (7)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem theorem_7 {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [Nonempty ι₁] [Nonempty ι₂]
    (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    MultiItemRev.Decomp.Rev (MultiItemRev.Decomp.jointLaw μY μZ) ≤ MultiItemRev.Decomp.Rev μY + MultiItemRev.Decomp.Rev μZ + MultiItemRev.Decomp.BRev μY + MultiItemRev.Decomp.BRev μZ ∧
      MultiItemRev.Decomp.Rev μY + MultiItemRev.Decomp.Rev μZ + MultiItemRev.Decomp.BRev μY + MultiItemRev.Decomp.BRev μZ ≤
        2 * (MultiItemRev.Decomp.Rev μY + MultiItemRev.Decomp.Rev μZ) := by sorry

end MultiItemRev.KBundling
