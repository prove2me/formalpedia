-- Prove2me | Theorems.Thm_OAI_Problem356_strictConvexOn_of_line_deriv2_pos
-- name    : OAI.Problem356.strictConvexOn_of_line_deriv2_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:13:12.693263+00:00
-- url     : https://prove2.me/theorems/7769a508-2044-4ef4-9d09-226a2cb62795
-- title:
--   Strict convexity from positive second derivatives along segments
-- statement:
--   Let $s$ be a convex subset of a real normed space and $f$ continuous on $s$. Suppose that for all distinct $x,y\in s$ and $t\in(0,1)$,
--   $$
--   \frac{d^2}{dt^2}f\bigl(x+t(y-x)\bigr)>0 .
--   $$
--   Then $f$ is strictly convex on $s$.
--
--   Strict convexity in any dimension reduces to one-variable second derivatives along line segments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StrictMinimum.lean#L50-L74

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity

open OAI OAI.Problem356
universe uE uP
open Set Filter
open scoped Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.Problem356.strictConvexOn_of_line_deriv2_pos {s : Set E} {f : E → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hpos : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < deriv (deriv (f ∘ AffineMap.lineMap x y)) t) :
    StrictConvexOn ℝ s f := by sorry
