-- Prove2me | Theorems.Thm_OAI_Problem356_map_squareDensity_localHomeomorph
-- name    : OAI.Problem356.map_squareDensity_localHomeomorph
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:22:48.118748+00:00
-- url     : https://prove2.me/theorems/87876f6a-badd-4829-ad06-56ecf189cab7
-- title:
--   Pushing a squared amplitude through a local homeomorphism
-- statement:
--   Let $e$ be a local homeomorphism of $\mathbb{R}^3$ whose inverse has derivative $D(y)$ on the target, and let $g$ have closed support inside the source. Then
--   $$
--   e_\#\bigl(g^2\,dx\bigr)=\Bigl(\mathbf{1}_{\mathrm{target}}\,(g\circ e^{-1})\sqrt{|\det D|}\Bigr)^2dy .
--   $$
--
--   The pushforward of a squared density is again a squared density, with the transported amplitude. This keeps the five-component density in the form required for a smooth square root.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SmoothPushforward.lean#L130-L159

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

theorem OAI.Problem356.map_squareDensity_localHomeomorph
    (e : OpenPartialHomeomorph E3 E3) (g : E3 → ℝ)
    (hgs : tsupport g ⊆ e.source)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (densityMeasure (fun x => g x ^ 2)) =
      densityMeasure (fun y =>
        localTransportAmplitude e g (fun z => Real.sqrt |(D z).det|) y ^ 2) := by sorry
