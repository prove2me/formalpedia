-- Prove2me | Theorems.Thm_OAI_Problem356_Splitting_not_preserving_of_countable_compression
-- name    : OAI.Problem356.Splitting.not_preserving_of_countable_compression
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:45:23.701192+00:00
-- url     : https://prove2.me/theorems/1520d79b-f59e-477a-8116-d78e6ebda8d7
-- title:
--   No measure-preserving map compresses mass
-- statement:
--   Let $\mu,\nu$ be measures with $\nu$ finite and nonzero, $c,d\in[0,\infty]$ with $d<c$, and countably many sets $S_i$ and measurable sets $A_i$. Suppose $T$ maps $S_i$ into $A_i$, and
--   $$
--   \mu(S_i)=c\,\nu(S_i),\qquad\mu(A_i)=d\,\nu(S_i),
--   $$
--   and the $S_i$ cover $\nu$-almost everything. Then $T$ is not a measurable map with $T_\#\mu=\mu$.
--
--   A preserving map cannot send each piece of the central component into a target of strictly smaller mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/Splitting.lean#L42-L65

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

open OAI OAI.Problem356
universe uAlpha uIndex
open MeasureTheory
open scoped ENNReal
variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

theorem OAI.Problem356.Splitting.not_preserving_of_countable_compression [Countable ι]
    {μ ν : Measure α} [IsFiniteMeasure ν]
    {T : α → α} {S A : ι → Set α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0)
    (hA : ∀ i, MeasurableSet (A i))
    (hsub : ∀ i, S i ⊆ T ⁻¹' A i)
    (hsource : ∀ i, μ (S i) = c * ν (S i))
    (htarget : ∀ i, μ (A i) = d * ν (S i))
    (hdc : d < c)
    (hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i) :
    ¬ (Measurable T ∧ Measure.map T μ = μ) := by sorry
