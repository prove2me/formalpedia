-- Prove2me | Theorems.Thm_OAI_Problem356_Transport_exists_measurable_lift_close
-- name    : OAI.Problem356.Transport.exists_measurable_lift_close
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:58:29.080344+00:00
-- url     : https://prove2.me/theorems/21a8de5b-4f5a-4065-a85b-5d502d3541f9
-- title:
--   Lifts whose source coordinate moves arbitrarily little
-- statement:
--   Let $X$ be a standard Borel metric space, $Y$ standard Borel, $\mu$ finite atomless on $X$ and carried by a compact set $K$, $\nu$ finite on $Y$, and $f:Y\to X$ measurable with $f_\#\nu=\mu$. Then for every $\delta>0$ there is a measurable $Q:X\to Y$ with
--   $$
--   Q_\#\mu=\nu,\qquad d\bigl(x,f(Qx)\bigr)<\delta\ \text{ for }\mu\text{-a.e. }x .
--   $$
--
--   Applied with $f$ the first projection of a coupling, this gives a map whose graph almost reproduces the coupling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CellwiseLift.lean#L73-L99

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

open OAI OAI.Problem356
universe uX uY uIndex
open MeasureTheory Set
open scoped ENNReal

theorem OAI.Problem356.Transport.exists_measurable_lift_close
    {X : Type uX} {Y : Type uY} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f) (hmarg : ν.map f = μ)
    {K : Set X} (hK : IsCompact K) (hfull : μ Kᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, dist x (f (Q x)) < δ := by sorry
