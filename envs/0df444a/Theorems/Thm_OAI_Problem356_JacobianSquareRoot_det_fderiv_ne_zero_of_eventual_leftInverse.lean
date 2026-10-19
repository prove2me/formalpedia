-- Prove2me | Theorems.Thm_OAI_Problem356_JacobianSquareRoot_det_fderiv_ne_zero_of_eventual_leftInverse
-- name    : OAI.Problem356.JacobianSquareRoot.det_fderiv_ne_zero_of_eventual_leftInverse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:36:31.850803+00:00
-- url     : https://prove2.me/theorems/b03579e0-2b3a-4a57-9a6b-9663d6c413f7
-- title:
--   A differentiable local left inverse forces a nonzero Jacobian
-- statement:
--   Let $E$ be a real normed space, $F,G:E\to E$ with $F$ differentiable at $x$, $G$ differentiable at $F(x)$, and $G(F(y))=y$ for $y$ near $x$. Then
--   $$
--   \det DF(x)\ne0 .
--   $$
--
--   Local charts with differentiable inverses have invertible derivatives. So their Jacobian square roots are smooth and the transported densities stay smooth.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/JacobianSquareRoot.lean#L82-L98

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

open OAI OAI.Problem356
universe uIndex uE uD
open MeasureTheory Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

theorem OAI.Problem356.JacobianSquareRoot.det_fderiv_ne_zero_of_eventual_leftInverse
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → E} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G (F x))
    (hGF : ∀ᶠ y in nhds x, G (F y) = y) : (fderiv ℝ F x).det ≠ 0 := by sorry
