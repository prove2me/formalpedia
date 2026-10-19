-- Prove2me | Theorems.Thm_OAI_Problem356_exists_normalized_smooth_square_in_ball
-- name    : OAI.Problem356.exists_normalized_smooth_square_in_ball
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:21:30.504789+00:00
-- url     : https://prove2.me/theorems/ee0ca132-d768-4f2e-9787-0f90e3d81677
-- title:
--   Normalized smooth amplitudes supported in any ball
-- statement:
--   For every $c\in\mathbb{R}^3$ and $r>0$ there is a function $g\ge0$ on $\mathbb{R}^3$ that is smooth with compact support inside the open ball $B(c,r)$, and
--   $$
--   \int_{\mathbb{R}^3}g^2=1 .
--   $$
--
--   The central component of the counterexample density is the square of such an amplitude.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/Density.lean#L48-L88

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

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.exists_normalized_smooth_square_in_ball (c : E3) {r : ℝ} (hr : 0 < r) :
    ∃ g : E3 → ℝ,
      (∀ x, 0 ≤ g x) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
      HasCompactSupport g ∧
      tsupport g ⊆ Metric.ball c r ∧
      (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1 := by sorry
