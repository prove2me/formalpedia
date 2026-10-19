-- Prove2me | Theorems.Thm_OAI_Problem356_Geometry_finite_disjoint_closedBalls_subset
-- name    : OAI.Problem356.Geometry.finite_disjoint_closedBalls_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:30:39.115157+00:00
-- url     : https://prove2.me/theorems/283df1b8-1315-40ec-a075-43145fc1259e
-- title:
--   Disjoint closed balls inside prescribed neighborhoods
-- statement:
--   Let $a_i$ ($i$ finite) be pairwise distinct points of a metric space and $U_i$ open sets with $a_i\in U_i$. Then there is $\delta>0$ such that
--   $$
--   \bar B(a_i,\delta)\subseteq U_i\quad\text{for all }i,
--   $$
--   and the closed balls $\bar B(a_i,\delta)$ are pairwise disjoint.
--
--   One radius simultaneously separates the components and keeps each inside the domain of its local certificate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/NeighborhoodCertificate.lean#L63-L89

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

theorem OAI.Problem356.Geometry.finite_disjoint_closedBalls_subset {ι : Type uIndex} {X : Type uX} [Finite ι]
    [MetricSpace X] (a : ι → X) (ha : Function.Injective a)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (haU : ∀ i, a i ∈ U i) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, closedBall (a i) δ ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by sorry
