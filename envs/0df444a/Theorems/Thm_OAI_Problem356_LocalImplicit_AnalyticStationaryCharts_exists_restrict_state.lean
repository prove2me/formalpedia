-- Prove2me | Theorems.Thm_OAI_Problem356_LocalImplicit_AnalyticStationaryCharts_exists_restrict_state
-- name    : OAI.Problem356.LocalImplicit.AnalyticStationaryCharts.exists_restrict_state
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:07:24.107883+00:00
-- url     : https://prove2.me/theorems/838c56fc-1019-480d-808b-9061e3a18d67
-- title:
--   Shrinking the state domain of stationary charts
-- statement:
--   Let $c$ be analytic stationary charts for $G$ at $(p,s)$ with state domain $V$, and let $W\subseteq V$ be open with $s\in W$. Then there are analytic stationary charts $d$ at $(p,s)$ with
--   $$
--   \mathrm{stateDomain}(d)=W,\qquad\mathrm{source}(d)\subseteq\mathrm{source}(c),
--   $$
--   and the same chart functions as $c$.
--
--   Any smaller state neighborhood can be used, at the cost of shrinking the parameter domain. All uniqueness conclusions are preserved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean#L247-L273

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

open OAI OAI.Problem356 OAI.Problem356.LocalImplicit OAI.Problem356.LocalImplicit.AnalyticStationaryCharts
universe uP uS
open Filter Set
open scoped Topology ContDiff
variable {P : Type uP} {S : Type uS}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
variable {G : P × (S × S) → S × S} {p : P} {s : S × S}
omit [CompleteSpace P] [CompleteSpace S]

theorem OAI.Problem356.LocalImplicit.AnalyticStationaryCharts.exists_restrict_state
    (c : AnalyticStationaryCharts G p s) (W : Set (S × S))
    (hW : IsOpen W) (hsW : s ∈ W) (hWV : W ⊆ c.stateDomain) :
    ∃ d : AnalyticStationaryCharts G p s,
      d.stateDomain = W ∧ d.central.source ⊆ c.central.source ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by sorry
