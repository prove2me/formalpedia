-- Prove2me | Theorems.Thm_MultiItemRev_Decomp_proposition_6_iii
-- name    : MultiItemRev.Decomp.proposition_6_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:33.527483+00:00
-- url     : https://prove2.me/theorems/f00b72fb-9579-45a5-bb64-4b315af5074c
-- title:
--   Proposition 6 (iii), p. 14 — Rev(X) is the supremum over IC, IR and NPT mechanisms
-- statement:
--   Let $X$ be a $k$-good random valuation in $\mathbb{R}^k_+$, $k \ge 1$. Then the optimal revenue can be computed over mechanisms with no positive transfer:
--   $$
--   \mathrm{Rev}(X) = \sup\{ R(\mu; X) : \mu \text{ is IC, IR and NPT} \}.
--   $$
--
--   No positive transfers ($s \ge 0$) can thus be assumed without loss of generality when maximizing revenue. This is what allows the revenue from a mechanism to be split over two regions of the valuation space that cover it, as in the proofs of Theorem A and Theorem 7.
--
--   **Formalization Note** The supremum ranges over mechanisms in the class $\mathcal M$ (IC, IR, $q \in [0,1]^k$, measurable $s$) that are also NPT; their revenues are nonnegative, so the clipping to $[0,\infty]$ in `toENNReal` is the identity on them.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 14, Proposition 6 (iii)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

theorem proposition_6_iii {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ≥0)) [IsProbabilityMeasure μ] :
    Rev μ = ⨆ (M : Mechanism ι) (_ : IsAdmissible M ∧ IsNPT M), (expRevenue μ M).toENNReal := by sorry

end MultiItemRev.Decomp
