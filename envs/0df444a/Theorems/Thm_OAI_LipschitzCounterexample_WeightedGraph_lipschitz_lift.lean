-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_WeightedGraph_lipschitz_lift
-- name    : OAI.LipschitzCounterexample.WeightedGraph.lipschitz_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:25:07.990132+00:00
-- url     : https://prove2.me/theorems/cb8d30c9-da14-4b65-9c7e-8d0091dc54aa
-- title:
--   Coordinatewise lifts between weighted graph spaces are Lipschitz
-- statement:
--   Let $Q:A\to H$ and $R:B\to J$ be bounded operators, and let $F:A\to B$ and $g:H\to J$ be Lipschitz with constants $K$ and $L$, with $F(0)=0$, $g(0)=0$ and $R\circ F=g\circ Q$. Then the lift $\mathcal G(Q)\to\mathcal G(R)$, which applies $F$ to every coordinate, is
--   $$
--   \max(K,L)\text{-Lipschitz}.
--   $$
--
--   In particular a bi-Lipschitz pair $(F,g)$ compatible with the operators induces a bi-Lipschitz map of weighted graph spaces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/WeightedGraph.lean#L199-L234

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeightedGraph
universe uA uH uB uJ
open scoped ENNReal NNReal Topology
open Filter
variable {A : Type uA} {H : Type uH} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (Q : A →L[ℝ] H)
variable {B : Type uB} {J : Type uJ} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
variable (R : B →L[ℝ] J) (F : A → B) (g : H → J)
  {K L : ℝ≥0} (hF : LipschitzWith K F) (hg : LipschitzWith L g)
  (hF0 : F 0 = 0) (hg0 : g 0 = 0) (hdiag : ∀ x, R (F x) = g (Q x))

theorem OAI.LipschitzCounterexample.WeightedGraph.lipschitz_lift : LipschitzWith (max K L) (lift Q R F g hF hg hF0 hg0 hdiag) := by sorry
