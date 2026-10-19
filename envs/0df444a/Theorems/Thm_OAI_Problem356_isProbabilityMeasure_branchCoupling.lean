-- Prove2me | Theorems.Thm_OAI_Problem356_isProbabilityMeasure_branchCoupling
-- name    : OAI.Problem356.isProbabilityMeasure_branchCoupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:36:50.235681+00:00
-- url     : https://prove2.me/theorems/abc6cb5c-7710-43d1-81ee-ae77d8bc2850
-- title:
--   The branch coupling is a probability measure
-- statement:
--   For a measure $\nu$ on $\mathbb{R}^3$ and maps $H_1,\dots,H_4$, the branch coupling is $\frac16$ times the sum of the pushforwards of $\nu$ under the six maps $x\mapsto(x,H_1x,H_2x)$, $(H_1x,H_2x,x)$, $(H_2x,x,H_1x)$, $(x,H_3x,H_4x)$, $(H_3x,H_4x,x)$, $(H_4x,x,H_3x)$. If $\nu$ is a probability measure and $H_1,\dots,H_4$ are measurable, then the branch coupling $\pi$ is a probability measure:
--   $$
--   \pi\bigl((\mathbb{R}^3)^3\bigr)=1 .
--   $$
--
--   The six pushforwards each have mass one, and the weight $\frac16$ normalizes their sum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/BranchCoupling.lean#L119-L133

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.isProbabilityMeasure_branchCoupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchCoupling nu H1 H2 H3 H4) := by sorry
