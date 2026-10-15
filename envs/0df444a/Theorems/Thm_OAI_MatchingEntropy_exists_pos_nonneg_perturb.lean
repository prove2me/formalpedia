-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_exists_pos_nonneg_perturb
-- name    : OAI.MatchingEntropy.exists_pos_nonneg_perturb
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:01:27.289505+00:00
-- url     : https://prove2.me/theorems/f7db9f9b-ab09-46de-bed1-deac9cddfa85
-- title:
--   A nonnegative vector stays nonnegative for some positive step in any direction that does not point outwards
-- statement:
--   Let $I$ be a finite index set, let $p\in\mathbb{R}^I$ have nonnegative coordinates, and let $v\in\mathbb{R}^I$ be a direction that does not point out of the nonnegative orthant at the zero coordinates of $p$: $v_i\ge0$ whenever $p_i=0$. Then there is a step $t>0$ such that
--   $$
--   p_i+t\,v_i\ge0\qquad\text{for every }i\in I .
--   $$
--
--   Equivalently, every such direction is a feasible direction for the cone $\mathbb{R}_{\ge0}^I$ at $p$. Coordinates with $p_i>0$ may move in either sense for a short time, while zero coordinates must not decrease. The result is used to make one-sided perturbations of probability vectors, for instance in directional-derivative arguments at the boundary of the probability simplex.
--
--   **Formalization Note** The conclusion is an existential statement $\exists\,t>0$ with the inequalities for all indices. No explicit value of $t$ is produced.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean#L188-L210

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.exists_pos_nonneg_perturb {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, p i = 0 → 0 ≤ v i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ p i+t*v i := by sorry
