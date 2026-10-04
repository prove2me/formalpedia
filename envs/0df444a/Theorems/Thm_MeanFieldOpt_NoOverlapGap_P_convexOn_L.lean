-- Prove2me | Theorems.Thm_MeanFieldOpt_NoOverlapGap_P_convexOn_L
-- name    : MeanFieldOpt.NoOverlapGap.P_convexOn_L
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:44:05.805814+00:00
-- url     : https://prove2.me/theorems/1a1a6de4-ca45-4e0b-b0eb-bb787b3e20db
-- title:
--   Section 6.3 — the Parisi functional $\mathsf P$ is convex on $\mathscr L$
-- statement:
--   Let $\xi$ be a mixture. The space $\mathscr L$ is a convex set of functions, and the Parisi functional
--
--   $$\mathsf P : \mathscr L \to \mathbb R$$
--
--   is convex on it: for $\gamma_0, \gamma_1 \in \mathscr L$ and $s \in [0,1]$,
--
--   $$\mathsf P\big((1-s)\gamma_0 + s\gamma_1\big) \le (1-s)\,\mathsf P(\gamma_0) + s\,\mathsf P(\gamma_1).$$
--
--   The paper states this in Section 6.3 and attributes it to the proof of [JT16, Theorem 20]. Together with the stationarity of a strictly increasing minimiser, convexity turns a critical point into a global minimiser over $\mathscr L$.
--
--   **Formalization Note** Stated as Mathlib's `ConvexOn` on the set of functions $\mathbb R \to \mathbb R$ satisfying the membership predicate of $\mathscr L$; `ConvexOn` includes convexity of that set.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 34, Section 6.3, second paragraph (citing [JT16, Theorem 20])

import Mathlib
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Spaces
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Parisi

open MeasureTheory Set

namespace MeanFieldOpt.NoOverlapGap

/-- Section 6.3 (arXiv:2001.00904v1, p. 34): the Parisi functional `P : ℒ → ℝ` is convex. -/
theorem P_convexOn_L (ξ : Mixture) : ConvexOn ℝ {γ : ℝ → ℝ | InL ξ γ} (P ξ) := by sorry

end MeanFieldOpt.NoOverlapGap
