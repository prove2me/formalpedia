-- Prove2me | Theorems.Thm_OAI_Problem356_Splitting_splitMeasure_apply_image
-- name    : OAI.Problem356.Splitting.splitMeasure_apply_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:47:06.712692+00:00
-- url     : https://prove2.me/theorems/fc9e05e5-bf20-413d-8f71-f39bc1da023a
-- title:
--   Mass of a split measure on a branch image
-- statement:
--   Let $\nu$ be carried by $B$, with maps $H_i$ measurable and injective on $B$, such that $B$ is disjoint from every $H_i(B)$ and the $H_i(B)$ are pairwise disjoint. For the split measure $a\nu+\sum_ib_iH_{i\#}\nu$ and $S\subseteq B$ with measurable images,
--   $$
--   \Bigl(a\nu+\sum_ib_iH_{i\#}\nu\Bigr)\bigl(H_j(S)\bigr)=b_j\,\nu(S) .
--   $$
--
--   Only the summand of branch $j$ contributes on its own image.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SplitMeasure.lean#L99-L124

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
variable [Fintype ι]

theorem OAI.Problem356.Splitting.splitMeasure_apply_image
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hInj : ∀ i, Set.InjOn (H i) B)
    (hSB : S ⊆ B) (hImage : ∀ i, MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) (j : ι) :
    splitMeasure ν a b H (H j '' S) = b j * ν S := by sorry
