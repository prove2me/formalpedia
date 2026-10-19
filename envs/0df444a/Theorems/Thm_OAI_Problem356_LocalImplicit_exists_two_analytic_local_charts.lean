-- Prove2me | Theorems.Thm_OAI_Problem356_LocalImplicit_exists_two_analytic_local_charts
-- name    : OAI.Problem356.LocalImplicit.exists_two_analytic_local_charts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:06:20.93001+00:00
-- url     : https://prove2.me/theorems/7fc09194-82e5-4605-9929-2880fd4ee308
-- title:
--   Both components of a branch are analytic charts on a common source
-- statement:
--   Let $P$ and $S$ be real Banach spaces. Let $\psi:P\to S\times S$ be analytic at $p$, $U$ a neighborhood of $p$, and suppose both components $\psi_1,\psi_2$ have invertible derivatives at $p$. Then there are local homeomorphisms $e_1,e_2$ with $e_1=\psi_1$, $e_2=\psi_2$ and a common source
--   $$
--   p\in\mathrm{source}(e_1)=\mathrm{source}(e_2)\subseteq U,
--   $$
--   such that $e_1,e_2$ and their inverses are analytic.
--
--   The central and opposite coordinates of a stationary branch become two genuine analytic charts over the same parameter set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean#L98-L132

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
theorem OAI.Problem356.LocalImplicit.exists_two_analytic_local_charts
    (ψ : P → S × S) (p : P) (U : Set P) (hU : U ∈ 𝓝 p)
    (hψ : ContDiffAt ℝ ω ψ p)
    (hinv₁ : (fderiv ℝ (fun y => (ψ y).1) p).IsInvertible)
    (hinv₂ : (fderiv ℝ (fun y => (ψ y).2) p).IsInvertible) :
    ∃ e₁ e₂ : OpenPartialHomeomorph P S,
      (e₁ : P → S) = (fun y => (ψ y).1) ∧
      (e₂ : P → S) = (fun y => (ψ y).2) ∧
      p ∈ e₁.source ∧ e₁.source = e₂.source ∧ e₁.source ⊆ U ∧
      ContDiffOn ℝ ω e₁ e₁.source ∧ ContDiffOn ℝ ω e₁.symm e₁.target ∧
      ContDiffOn ℝ ω e₂ e₂.source ∧ ContDiffOn ℝ ω e₂.symm e₂.target := by sorry
