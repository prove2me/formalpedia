-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_theorem_7
-- name    : MultiItemRev.KSeparate.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:38.526877+00:00
-- url     : https://prove2.me/theorems/613f9bdd-8701-4194-a47e-417dc0c69b72
-- title:
--   Theorem 7, p. 18 — revenue decomposition for independent groups
-- statement:
--   Let $Y$ and $Z$ be independent nonempty groups of nonnegative goods. Coordinates within either group may be dependent. Their joint optimal revenue satisfies both inequalities
--
--   $$\operatorname{Rev}(Y,Z)\le\operatorname{Rev}(Y)+\operatorname{Rev}(Z)+\operatorname{BRev}(Y)+\operatorname{BRev}(Z)\le2\bigl(\operatorname{Rev}(Y)+\operatorname{Rev}(Z)\bigr).$$
--
--   The first inequality is the decomposition step in the proof of Theorem C. **Formalization Note** The joint law is constructed as a product of the two vector laws, so independence is part of the object rather than an independent hypothesis.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 18, Theorem 7, (6)–(7)

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem theorem_7 {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [Nonempty ι₁] [Nonempty ι₂]
    (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    MultiItemRev.Decomp.Rev (MultiItemRev.Decomp.jointLaw μY μZ) ≤ MultiItemRev.Decomp.Rev μY + MultiItemRev.Decomp.Rev μZ + MultiItemRev.Decomp.BRev μY + MultiItemRev.Decomp.BRev μZ ∧
      MultiItemRev.Decomp.Rev μY + MultiItemRev.Decomp.Rev μZ + MultiItemRev.Decomp.BRev μY + MultiItemRev.Decomp.BRev μZ ≤
        2 * (MultiItemRev.Decomp.Rev μY + MultiItemRev.Decomp.Rev μZ) := by sorry

end MultiItemRev.KSeparate
