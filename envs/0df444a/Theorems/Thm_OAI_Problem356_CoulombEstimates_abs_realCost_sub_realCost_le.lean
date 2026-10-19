-- Prove2me | Theorems.Thm_OAI_Problem356_CoulombEstimates_abs_realCost_sub_realCost_le
-- name    : OAI.Problem356.CoulombEstimates.abs_realCost_sub_realCost_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:42:34.705105+00:00
-- url     : https://prove2.me/theorems/db50a57b-32e8-4c17-a3d6-6884e35f1700
-- title:
--   Oscillation of the Coulomb cost on separated triples
-- statement:
--   In a metric space, let $(x,y,z)$ and $(x',y',z')$ be $\eta$-separated triples, all pairwise distances $\ge\eta>0$, with $d(x,x'),d(y,y'),d(z,z')\le\delta$. Then
--   $$
--   \bigl|c(x,y,z)-c(x',y',z')\bigr|\le\frac{6\delta}{\eta^2},
--   $$
--   where $c$ is the real three-body Coulomb cost $\sum_{\text{pairs}}d^{-1}$.
--
--   On separated configurations the Coulomb cost is Lipschitz. This controls the error when triples are moved within small cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombEstimates.lean#L71-L96

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates

open OAI OAI.Problem356 OAI.Problem356.CoulombEstimates
universe uE uA
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.CoulombEstimates.abs_realCost_sub_realCost_le {E : Type uE} [PseudoMetricSpace E]
    {x y z x' y' z' : E} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    |realCost x y z - realCost x' y' z'| ≤ (6 * delta) / eta ^ 2 := by sorry
