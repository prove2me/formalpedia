-- Prove2me | Theorems.Thm_OAI_Problem356_SmoothBranchMarginal_componentRegion_pairwise_of_subsets
-- name    : OAI.Problem356.SmoothBranchMarginal.componentRegion_pairwise_of_subsets
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:53:04.275554+00:00
-- url     : https://prove2.me/theorems/d2cd3bd2-4796-4475-ba5a-1292660b4ea9
-- title:
--   Component regions inside disjoint sets are disjoint
-- statement:
--   Let $U_0,\dots,U_4$ be pairwise disjoint sets, $B\subseteq U_0$, and local homeomorphisms $e_0,\dots,e_3$ with $e_i(B)\subseteq U_{i+1}$. Then the five component regions
--   $$
--   B,\ e_0(B),\ e_1(B),\ e_2(B),\ e_3(B)
--   $$
--   are pairwise disjoint.
--
--   Placing the components inside the disjoint certificate balls supplies the disjointness required by the smooth marginal construction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/ComponentRegions.lean#L9-L29

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
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterAxis

open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal

theorem OAI.Problem356.SmoothBranchMarginal.componentRegion_pairwise_of_subsets
    {B : Set E3} {e : Fin 4 → OpenPartialHomeomorph E3 E3}
    {U : Fin 5 → Set E3}
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hB : B ⊆ U 0) (he : ∀ i, e i '' B ⊆ U i.succ) :
    Pairwise (fun i j => Disjoint (componentRegion B e i) (componentRegion B e j)) := by sorry
