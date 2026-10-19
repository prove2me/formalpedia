-- Prove2me | Theorems.Thm_OAI_Problem356_bilinear_coercive_of_norm_sub_le
-- name    : OAI.Problem356.bilinear_coercive_of_norm_sub_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:16:13.665128+00:00
-- url     : https://prove2.me/theorems/8b8cd36c-412e-41d8-ae5f-f0dbb8fe3776
-- title:
--   Coercivity survives small perturbations of a bilinear form
-- statement:
--   Let $B,C$ be continuous bilinear forms on a real normed space with $B(v,v)\ge a|v|^2$ for all $v$ and $\|C-B\|\le\delta$. Then
--   $$
--   C(v,v)\ge(a-\delta)|v|^2\qquad\text{for all }v .
--   $$
--
--   No finite-dimensionality is needed. This transfers positivity of the Hessian at the center to a neighborhood.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/HessianCoercivity.lean#L12-L29

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
universe uE uX
open Filter
open scoped Topology

theorem OAI.Problem356.bilinear_coercive_of_norm_sub_le
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (a δ : ℝ)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v) (hclose : ‖C - B‖ ≤ δ) :
    ∀ v, (a - δ) * ‖v‖ ^ 2 ≤ C v v := by sorry
