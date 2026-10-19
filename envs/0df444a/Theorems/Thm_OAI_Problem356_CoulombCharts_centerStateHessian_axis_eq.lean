-- Prove2me | Theorems.Thm_OAI_Problem356_CoulombCharts_centerStateHessian_axis_eq
-- name    : OAI.Problem356.CoulombCharts.centerStateHessian_axis_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:09:59.552979+00:00
-- url     : https://prove2.me/theorems/23a50d15-f074-4f8f-aff5-6cb8f1156c2a
-- title:
--   The computed state derivative is the certified operator
-- statement:
--   For an axis $k$, let $Q_k$ be the Hessian of $|x|^{-1}$ at the unit vector $e_k$, which is diagonal with eigenvalues $2$ along $e_k$ and $-1$ transversely. With $K=20$, the state derivative
--   $$
--   (u_1,u_2)\mapsto\bigl((2Q_k+20)u_1-Q_ku_2,\ -Q_ku_1+(\tfrac98Q_k+20)u_2\bigr)
--   $$
--   equals the regularized $6\times6$ Hessian operator of axis $k$, written in product coordinates.
--
--   The analytic derivative agrees with the matrix whose invertibility is checked by finite-dimensional algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombCharts.lean#L15-L30

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

theorem OAI.Problem356.CoulombCharts.centerStateHessian_axis_eq (k : Fin 3) :
    centerStateHessian 20 (CoulombCalculus.pairHessian (axisVector k)) =
      LocalHessian.stateOperator k := by sorry
