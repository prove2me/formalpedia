-- Prove2me | Theorems.Thm_OAI_Problem356_LocalGeometry_nonempty_localSupportingCharts
-- name    : OAI.Problem356.LocalGeometry.nonempty_localSupportingCharts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:18:51.454966+00:00
-- url     : https://prove2.me/theorems/174698e1-08ad-456f-a2a0-30b49a2da3f3
-- title:
--   Local supporting charts from a positive Hessian
-- statement:
--   Let $E$ be a finite-dimensional real Banach space, $F:E\times(E\times E)\to\mathbb{R}$ analytic at $(p,s)$, and suppose that near $(p,s)$ the state derivative of $F$ is $D$ and the derivative of $D$ is $H$, continuous at $(p,s)$, with
--   $$
--   H(p,s)(v,v)>0\qquad(v\ne0).
--   $$
--   Let $G$ be a map whose zeros are critical points of $F$ in the state, i.e. $G=0\Rightarrow D=0$, and suppose analytic stationary charts for $G$ exist at $(p,s)$. Then local supporting charts exist: for each parameter $y$ near $p$, the branch point is the unique minimizer of $F(y,\cdot)$ on a state ball around $s$.
--
--   Positivity of the Hessian at the base point yields the neighborhood-level supporting certificate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalCertificate.lean#L38-L143

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

open OAI OAI.Problem356 OAI.Problem356.LocalGeometry
universe uE
open Set Filter
open scoped Topology ContDiff
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.Problem356.LocalGeometry.nonempty_localSupportingCharts [CompleteSpace E] [FiniteDimensional ℝ E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E}
    {D : E → (E × E) → (E × E) →L[ℝ] ℝ}
    {H : E → (E × E) → (E × E) →L[ℝ] ((E × E) →L[ℝ] ℝ)}
    {p : E} {s : E × E}
    (C : LocalImplicit.AnalyticStationaryCharts G p s)
    (hF : ContDiffAt ℝ ω F (p, s))
    (hD : ∀ᶠ q in 𝓝 (p, s), HasFDerivAt (fun z => F (q.1, z)) (D q.1 q.2) q.2)
    (hH : ∀ᶠ q in 𝓝 (p, s), HasFDerivAt (D q.1) (H q.1 q.2) q.2)
    (hHcont : ContinuousAt (fun q : E × (E × E) => H q.1 q.2) (p, s))
    (hHpos : ∀ v : E × E, v ≠ 0 → 0 < H p s v v)
    (hcompatible : ∀ q : E × (E × E), G q = 0 → D q.1 q.2 = 0) :
    Nonempty (LocalSupportingCharts F G p s) := by sorry
