-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_9
-- name    : OnlineMaxWeightMatch.Approx.lemma_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:51.661863+00:00
-- url     : https://prove2.me/theorems/b1f47820-e054-43ac-9095-26e9b6d069a1
-- title:
--   Lemma 4.9: the early-occupancy indicators {O^E_{i,t}}_i are negatively associated
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   For every ball $t$, the family of indicators
--
--   $$
--   \big\{O^E_{i,t}\big\}_{i},
--   $$
--
--   indexed by the bins $i$, where $O^E_{i,t}$ indicates that bin $i$ has been matched along an early edge before $t$ arrives, is negatively associated (Definition 2.5).
--
--   This is the negative-dependence step of the analysis: early matches of different bins cannot be positively correlated.
--
--   **Formalization Note** The family ranges over all bins of the instance the algorithm is run on (including dummy bins when it is the augmented instance).
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 15, Lemma 4.9

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Lemma 4.9. For any time `t`, the variables `{O^E_{i,t}}_i` are negatively associated. -/
theorem lemma_4_9 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (t : Fin n) :
    NegativelyAssociated (fun i => occupancyEarly x i t) (algMeasure I x) := by sorry

end OnlineMaxWeightMatch.Approx
