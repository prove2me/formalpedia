-- Prove2me | Theorems.Thm_OAI_Problem356_CoulombCharts_nonempty_coulombCharts
-- name    : OAI.Problem356.CoulombCharts.nonempty_coulombCharts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:10:44.024081+00:00
-- url     : https://prove2.me/theorems/fba9c7e5-6e2f-4924-93ac-a09759efe554
-- title:
--   Local Coulomb branches exist at every axis reference triple
-- statement:
--   Let $\phi(x)=|x|^{-1}$ on a real inner product space $E$, $K\in\mathbb{R}$ and $|a|=1$. The stationarity map of the regularized local problem is $G(p,(z,w))=\bigl(\nabla\phi(z-p)+\nabla\phi(z-w)+Kz,\ -\nabla\phi(z-w)-\nabla\phi(p-w)-\frac54a+K(w+a)\bigr)$, with reference point $(p,(z,w))=(a,(0,-a))$. Take $K=20$ and $a=e_k$ a unit axis vector. Then analytic stationary charts exist for $G$ at
--   $$
--   (p,(z,w))=(e_k,(0,-e_k)) .
--   $$
--
--   So near the reference triple $(e_k,0,-e_k)$, the stationary configurations form a branch parametrized by the outer point, whose central and opposite coordinates are analytic local diffeomorphisms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombCharts.lean#L69-L84

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

open OAI OAI.Problem356
open scoped ContDiff
open CoulombCalculus GeometryJets LocalImplicit

theorem OAI.Problem356.CoulombCharts.nonempty_coulombCharts (k : Fin 3) :
    Nonempty (AnalyticStationaryCharts
      (stationaryEquation 20 (axisVector k)) (axisVector k) (0, -axisVector k)) := by sorry
