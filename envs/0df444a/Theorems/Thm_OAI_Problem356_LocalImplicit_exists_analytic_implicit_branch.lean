-- Prove2me | Theorems.Thm_OAI_Problem356_LocalImplicit_exists_analytic_implicit_branch
-- name    : OAI.Problem356.LocalImplicit.exists_analytic_implicit_branch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:04:44.873518+00:00
-- url     : https://prove2.me/theorems/5a218feb-ea97-4e86-ba1c-6951d70c7cea
-- title:
--   Analytic implicit function theorem on product neighborhoods
-- statement:
--   Let $P$ and $S$ be real Banach spaces. Let $G:P\times S\to S$ be analytic at $(p,s)$ with $G(p,s)=0$, and suppose the partial derivative $D_sG(p,s)$ is invertible. Then there are open sets $U\ni p$, $V\ni s$ and an analytic $\psi:U\to V$ with $\psi(p)=s$ such that for $y\in U$ and $z\in V$
--   $$
--   G(y,z)=0\iff z=\psi(y),
--   $$
--   and $\psi$ has strict derivative $-D_sG(p,s)^{-1}\circ D_pG(p,s)$ at $p$.
--
--   This is the analytic implicit function theorem, packaged with explicit open neighborhoods and uniqueness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean#L18-L54

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

theorem OAI.Problem356.LocalImplicit.exists_analytic_implicit_branch
    (G : P × S → S) (p : P) (s : S)
    (hG : ContDiffAt ℝ ω G (p, s))
    (hzero : G (p, s) = 0)
    (hinv : (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P S).IsInvertible) :
    ∃ (ψ : P → S) (U : Set P) (V : Set S),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ s ∈ V ∧
      ContDiffOn ℝ ω ψ U ∧ MapsTo ψ U V ∧ ψ p = s ∧
      (∀ y ∈ U, G (y, ψ y) = 0) ∧
      (∀ y ∈ U, ∀ z ∈ V, G (y, z) = 0 ↔ ψ y = z) ∧
      HasStrictFDerivAt ψ
        (-(fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P S).inverse ∘L
          (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ P S)) p := by sorry
