-- Prove2me | Theorems.Thm_OAI_Problem356_SmoothBranchMarginal_exists_smooth_branch_marginal
-- name    : OAI.Problem356.SmoothBranchMarginal.exists_smooth_branch_marginal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:38:38.688989+00:00
-- url     : https://prove2.me/theorems/066fee0b-19eb-44c7-9e28-a9ab3fca30ad
-- title:
--   Construction of the smooth five-component marginal
-- statement:
--   An amplitude $g$ on $\mathbb{R}^3$ is normalized if $g\ge0$, $g$ is smooth with compact support, and $\int g^2=1$. Let $B=B(c,r)$, and let $e_0,\dots,e_3$ be local homeomorphisms with $B$ in each source, smooth inverses with derivatives $D_i$ and smooth $\sqrt{|\det D_i|}$, such that $B,e_0(B),\dots,e_3(B)$ are pairwise disjoint. Then there are normalized amplitudes $g$ with support in $B$ and $q_i$ with support in $e_i(B)$ such that
--   $$
--   \rho=\tfrac13g^2+\tfrac16\sum_iq_i^2
--   $$
--   is a smooth compact probability density, and
--   $$
--   \rho\,dx=\tfrac13\,g^2dx+\tfrac16\sum_i\tilde e_{i\#}(g^2dx) .
--   $$
--
--   This is the actual counterexample density, assembled from local branch charts on a common ball.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SmoothBranchMarginal.lean#L162-L198

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
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal

open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal
open MeasureTheory Set
open scoped ENNReal

theorem OAI.Problem356.SmoothBranchMarginal.exists_smooth_branch_marginal
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    (D : Fin 4 → E3 → E3 →L[ℝ] E3)
    (hD : ∀ i y, y ∈ (e i).target → HasFDerivAt (e i).symm (D i y) y)
    (hJ : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D i y).det|) (e i).target) :
    ∃ (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ),
      NormalizedAmplitude g ∧ tsupport g ⊆ Metric.ball c r ∧
      (∀ i, NormalizedAmplitude (q i) ∧ tsupport (q i) ⊆ e i '' Metric.ball c r) ∧
      IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) ∧
      IsSmoothCompactProbabilityDensity (marginalDensity g q) ∧
      densityMeasure (marginalDensity g q) =
        (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
        ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) •
          Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
            (densityMeasure (fun x => g x ^ 2)) := by sorry
