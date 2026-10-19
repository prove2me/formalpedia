-- Prove2me | Theorems.Thm_OAI_Problem356_Transport_exists_measurable_transport_finite
-- name    : OAI.Problem356.Transport.exists_measurable_transport_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:36:19.614991+00:00
-- url     : https://prove2.me/theorems/d9bebce1-bf39-43a6-b276-e7deb3b22cf4
-- title:
--   Measurable transport between finite measures of equal mass
-- statement:
--   Let $X,Y$ be standard Borel spaces with $Y$ nonempty, and $\mu,\nu$ finite measures with $\mu(X)=\nu(Y)$, where $\mu$ has no atoms. Then there is a measurable $Q:X\to Y$ with
--   $$
--   Q_\#\mu=\nu .
--   $$
--
--   Mass can be moved between any two finite measures of equal total mass as long as the source is atomless.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/AtomlessTransport.lean#L46-L77

import Mathlib
import Definitions.Def_CoulombCounterexample

open OAI OAI.Problem356
universe uX uY
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal unitInterval

theorem OAI.Problem356.Transport.exists_measurable_transport_finite {X : Type uX} {Y : Type uY}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass μ]
    (hmass : μ univ = ν univ) :
    ∃ Q : X → Y, Measurable Q ∧ Measure.map Q μ = ν := by sorry
