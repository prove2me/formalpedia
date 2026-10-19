-- Prove2me | Theorems.Thm_OAI_Problem356_map_withDensity_localHomeomorph
-- name    : OAI.Problem356.map_withDensity_localHomeomorph
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:22:12.976676+00:00
-- url     : https://prove2.me/theorems/077b5dd1-e7b2-49d0-adaf-6f449fab4572
-- title:
--   Change of variables for a local homeomorphism
-- statement:
--   Let $e$ be a local homeomorphism of $\mathbb{R}^3$ whose inverse has derivative $D(y)$ at each $y$ in the target, and $w\ge0$ a density. Then
--   $$
--   e_\#\bigl(w\cdot\mathrm{Leb}|_{\mathrm{source}(e)}\bigr)=\bigl|\det D(y)\bigr|\,w(e^{-1}y)\cdot\mathrm{Leb}|_{\mathrm{target}(e)} .
--   $$
--
--   This is the inverse-Jacobian change of variables formula, needing only the local behavior of $e$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SmoothPushforward.lean#L94-L128

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
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem OAI.Problem356.map_withDensity_localHomeomorph
    (e : OpenPartialHomeomorph E3 E3) (w : E3 → ℝ≥0∞)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (((volume : Measure E3).restrict e.source).withDensity w) =
      ((volume : Measure E3).restrict e.target).withDensity
        (fun y => ENNReal.ofReal |(D y).det| * w (e.symm y)) := by sorry
