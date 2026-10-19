-- Prove2me | Theorems.Thm_OAI_Problem356_Splitting_map_image_eq
-- name    : OAI.Problem356.Splitting.map_image_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:46:28.802846+00:00
-- url     : https://prove2.me/theorems/9d72e083-9155-4398-82ba-33817b997b2e
-- title:
--   Pushforward mass of an injective branch on images
-- statement:
--   Let $\nu$ be carried by $B$, $H$ measurable and injective on $B$, $S\subseteq B$ with $H(S)$ measurable. Then
--   $$
--   (H_\#\nu)\bigl(H(S)\bigr)=\nu(S) .
--   $$
--
--   An injective branch carries exactly the mass of each central piece to its image.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SplitMeasure.lean#L39-L56

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

open OAI OAI.Problem356 OAI.Problem356.Splitting
universe uAlpha uIndex
open MeasureTheory Set
open scoped ENNReal
variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

theorem OAI.Problem356.Splitting.map_image_eq
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hInj : Set.InjOn H B) (hSB : S ⊆ B)
    (hImage : MeasurableSet (H '' S)) :
    (Measure.map H ν) (H '' S) = ν S := by sorry
