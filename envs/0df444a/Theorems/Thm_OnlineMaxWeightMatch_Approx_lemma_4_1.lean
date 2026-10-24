-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_1
-- name    : OnlineMaxWeightMatch.Approx.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:45.423114+00:00
-- url     : https://prove2.me/theorems/df589974-9456-41c1-917f-e427d9b4cd68
-- title:
--   Lemma 4.1: LP-Match(I) ≥ OPT_on(I)
-- statement:
--   For every RideHail instance $I$, the optimal value of the linear program LP-Match is at least the expected profit of the optimal online algorithm:
--
--   $$
--   \mathrm{LP\text{-}Match}(I)\ \ge\ \mathrm{OPT}_{on}(I).
--   $$
--
--   The lemma makes LP-Match a relaxation of the online problem; together with the per-edge guarantee of Theorem 4.2 it gives the approximation ratio of Theorem 1.2. It fails for the offline optimum, because Constraint (11) is not valid for offline algorithms.
--
--   **Formalization Note** $\mathrm{OPT}_{on}(I)$ is the supremum of the expected profit over deterministic non-anticipating online policies (definition `RideHail`); $\mathrm{LP\text{-}Match}(I)$ is the supremum of the LP objective over the feasible set (definition `LPMatch`).
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 10, Lemma 4.1

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_LPMatch

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Lemma 4.1. For any RideHail instance `I`, `LP-Match(I) ≥ OPT_on(I)`. -/
theorem lemma_4_1 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n) :
    optOn I ≤ lpValue I := by sorry

end OnlineMaxWeightMatch.Approx
