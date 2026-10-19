-- Prove2me | Theorems.Thm_OAI_Problem356_Transport_exists_measurable_lift_preserving_label
-- name    : OAI.Problem356.Transport.exists_measurable_lift_preserving_label
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:56:08.353772+00:00
-- url     : https://prove2.me/theorems/1db2c62d-184c-4b8b-ae18-2d6290d61bd8
-- title:
--   Lifting an atomless marginal while preserving a countable label
-- statement:
--   Let $X,Y$ be standard Borel spaces, $\mu$ a finite atomless measure on $X$, $\nu$ a finite measure on $Y$, and $f:Y\to X$ measurable with $f_\#\nu=\mu$. Let $p:X\to\iota$ be a measurable label with countable values. Then there is a measurable $Q:X\to Y$ with
--   $$
--   Q_\#\mu=\nu,\qquad p(f(Qx))=p(x)\ \text{ for }\mu\text{-a.e. }x .
--   $$
--
--   The lift reproduces the whole law $\nu$ exactly, while moving each point only within its label class.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CellwiseLift.lean#L17-L71

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

theorem OAI.Problem356.Transport.exists_measurable_lift_preserving_label
    {X : Type uX} {Y : Type uY} {ι : Type uIndex} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [Nonempty ι]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f)
    (hmarg : ν.map f = μ) (p : X → ι) (hp : Measurable p) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, p (f (Q x)) = p x := by sorry
