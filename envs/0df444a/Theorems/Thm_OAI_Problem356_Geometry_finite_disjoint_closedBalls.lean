-- Prove2me | Theorems.Thm_OAI_Problem356_Geometry_finite_disjoint_closedBalls
-- name    : OAI.Problem356.Geometry.finite_disjoint_closedBalls
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:30:08.900985+00:00
-- url     : https://prove2.me/theorems/7d265c07-3069-4abd-bf2a-7fe67031aa8b
-- title:
--   Disjoint closed balls around finitely many distinct centers
-- statement:
--   Let $a_i$ ($i$ finite) be pairwise distinct points of a metric space. Then there is $\delta>0$ such that the closed balls $\bar B(a_i,\delta)$ are pairwise disjoint:
--   $$
--   \bar B(a_i,\delta)\cap\bar B(a_j,\delta)=\emptyset\qquad(i\ne j) .
--   $$
--
--   The five component balls of the construction can be chosen pairwise disjoint.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/NeighborhoodCertificate.lean#L44-L61

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
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward

open OAI OAI.Problem356
universe uIndex uX
open Filter Metric Set

theorem OAI.Problem356.Geometry.finite_disjoint_closedBalls {ι : Type uIndex} {X : Type uX} [Finite ι] [MetricSpace X]
    (a : ι → X) (ha : Function.Injective a) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (fun i j =>
      Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by sorry
