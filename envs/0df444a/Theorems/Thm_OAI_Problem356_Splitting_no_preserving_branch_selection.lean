-- Prove2me | Theorems.Thm_OAI_Problem356_Splitting_no_preserving_branch_selection
-- name    : OAI.Problem356.Splitting.no_preserving_branch_selection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:45:57.440502+00:00
-- url     : https://prove2.me/theorems/36ae43b2-9887-4fc7-b5d5-4d2221507268
-- title:
--   No preserving map selects a branch almost everywhere
-- statement:
--   Let $\nu$ be finite and nonzero, carried by a measurable set $B$, and let $H_i$ ($i$ countable) be measurable maps with measurable images of measurable subsets of $B$. Suppose, for measurable $S\subseteq B$,
--   $$
--   \mu(S)=c\,\nu(S),\qquad\mu(H_i(S))=d\,\nu(S),\qquad d<c .
--   $$
--   Then there is no measurable $T$ with $T_\#\mu=\mu$ and $Tx\in\{H_ix\}_i$ for $\nu$-a.e. $x$.
--
--   In the counterexample the central component has weight $c=\frac13$ and each branch image has weight $d=\frac16$. So a deterministic map following the contact branches cannot preserve the marginal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/Splitting.lean#L67-L99

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

theorem OAI.Problem356.Splitting.no_preserving_branch_selection [Countable ι] [MeasurableEq α]
    {μ ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hsource : ∀ S, MeasurableSet S → S ⊆ B → μ S = c * ν S)
    (htarget : ∀ i S, MeasurableSet S → S ⊆ B →
      μ (H i '' S) = d * ν S)
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧ Measure.map T μ = μ ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by sorry
