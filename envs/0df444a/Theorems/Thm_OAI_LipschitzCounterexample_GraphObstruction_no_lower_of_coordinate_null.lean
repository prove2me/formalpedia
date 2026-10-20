-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_GraphObstruction_no_lower_of_coordinate_null
-- name    : OAI.LipschitzCounterexample.GraphObstruction.no_lower_of_coordinate_null
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:28:25.403755+00:00
-- url     : https://prove2.me/theorems/b3504ffc-4a5f-4616-9989-b8cb25c042a4
-- title:
--   Operators from ℓ² into c₀(H) with null coordinates are not bounded below
-- statement:
--   Let $T:\ell^2\to c_0(H)$ be a bounded operator into the space of null sequences in a normed space $H$. Suppose every coordinate of the images of the unit vectors tends to $0$:
--   $$
--   T(e_k)_i\to0\quad(k\to\infty)\ \text{for each }i .
--   $$
--   Then $T$ is not bounded below: there is no $b>0$ with $b\|x\|\le\|Tx\|$ for all $x$.
--
--   It is the basic step in showing that weighted graph spaces of completely continuous operators avoid $c_0(\ell^2)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/GraphObstruction.lean#L123-L185

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.GraphObstruction
universe uH uA uB
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
open NullSequences

theorem OAI.LipschitzCounterexample.GraphObstruction.no_lower_of_coordinate_null (T : RealL2 →L[ℝ] C0 (H := H))
    (hcoord : ∀ i, Tendsto (fun k => T (unitVector k) i) atTop (𝓝 0))
    (b : ℝ) (hb : 0 < b) (hlower : ∀ x, b * ‖x‖ ≤ ‖T x‖) : False := by sorry
