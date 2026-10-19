-- Prove2me | Theorems.Thm_OAI_Problem356_LocalImplicit_exists_analytic_local_diffeomorph
-- name    : OAI.Problem356.LocalImplicit.exists_analytic_local_diffeomorph
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:05:36.55527+00:00
-- url     : https://prove2.me/theorems/ed274b16-7bbd-42b1-8a3a-37062ce40e20
-- title:
--   Analytic inverse function theorem
-- statement:
--   Let $P$ and $S$ be real Banach spaces. If $f:P\to S$ is analytic at $p$ and $Df(p)$ is invertible, then there is a local homeomorphism $e$ with
--   $$
--   e=f,\qquad p\in\mathrm{source}(e),
--   $$
--   such that $e$ is analytic on its source and $e^{-1}$ is analytic on its target.
--
--   A map with invertible derivative at a point of analyticity is an analytic diffeomorphism near that point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean#L56-L96

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

open OAI OAI.Problem356 OAI.Problem356.LocalImplicit
universe uP uS
open Filter Set
open scoped Topology ContDiff
variable {P : Type uP} {S : Type uS}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

omit [CompleteSpace S] in
theorem OAI.Problem356.LocalImplicit.exists_analytic_local_diffeomorph
    (f : P → S) (p : P)
    (hf : ContDiffAt ℝ ω f p)
    (hinv : (fderiv ℝ f p).IsInvertible) :
    ∃ e : OpenPartialHomeomorph P S,
      (e : P → S) = f ∧ p ∈ e.source ∧
      ContDiffOn ℝ ω e e.source ∧ ContDiffOn ℝ ω e.symm e.target := by sorry
