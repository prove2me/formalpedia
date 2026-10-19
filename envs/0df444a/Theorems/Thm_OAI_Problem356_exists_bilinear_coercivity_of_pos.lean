-- Prove2me | Theorems.Thm_OAI_Problem356_exists_bilinear_coercivity_of_pos
-- name    : OAI.Problem356.exists_bilinear_coercivity_of_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:17:11.668315+00:00
-- url     : https://prove2.me/theorems/ea66dd09-8034-4b4c-8f3f-31eb6dc549e8
-- title:
--   Positive bilinear forms are coercive in finite dimension
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $B$ a continuous bilinear form with $B(v,v)>0$ for all $v\ne0$. Then there is $a>0$ with
--   $$
--   B(v,v)\ge a|v|^2\qquad\text{for all }v .
--   $$
--
--   Strict positivity at one point upgrades to a quantitative bound, which then survives small perturbations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/HessianCoercivity.lean#L48-L83

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

theorem OAI.Problem356.exists_bilinear_coercivity_of_pos
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ a : ℝ, 0 < a ∧ ∀ v, a * ‖v‖ ^ 2 ≤ B v v := by sorry
