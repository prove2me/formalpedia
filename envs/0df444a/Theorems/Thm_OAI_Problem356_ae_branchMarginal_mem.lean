-- Prove2me | Theorems.Thm_OAI_Problem356_ae_branchMarginal_mem
-- name    : OAI.Problem356.ae_branchMarginal_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:49:25.098713+00:00
-- url     : https://prove2.me/theorems/ca7cf55c-af93-4297-b937-cbc60b2cea94
-- title:
--   Support of the five-component marginal
-- statement:
--   Let $\nu$ be carried by $B$, $H_0,\dots,H_3$ measurable, and $U$ measurable with $B\subseteq U$ and $H_i(B)\subseteq U$. Then $U$ carries the branch marginal:
--   $$
--   \mu\bigl(\mathbb{R}^3\setminus U\bigr)=0,\qquad\mu=\tfrac13\nu+\tfrac16\sum_iH_{i\#}\nu .
--   $$
--
--   The marginal lives on the central set and its four images.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CounterexampleAssembly.lean#L23-L40

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

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.ae_branchMarginal_mem (nu : Measure E3) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) {B U : Set E3}
    (hU : MeasurableSet U) (hfull : ∀ᵐ x ∂nu, x ∈ B)
    (hBU : B ⊆ U) (hHU : ∀ i, H i '' B ⊆ U) :
    ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U := by sorry
