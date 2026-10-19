-- Prove2me | Theorems.Thm_OAI_Problem356_CommonBranches_exists_common_central_ball_in_components
-- name    : OAI.Problem356.CommonBranches.exists_common_central_ball_in_components
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:00:28.962764+00:00
-- url     : https://prove2.me/theorems/e7492331-7116-4613-8206-7287b4c09df9
-- title:
--   A central ball keeping all branches in prescribed neighborhoods
-- statement:
--   Let $X_i,Z_i$ ($i$ finite) be local homeomorphisms of a metric space with base points $a_i$ in both sources, $X_i(a_i)=x$ for all $i$, open sets $P_i\ni a_i$ and $Q_i\ni Z_i(a_i)$, and an open $U\ni x$. Then there is $r>0$ with $B(x,r)\subseteq U$ such that for all $i$ and $y\in B(x,r)$,
--   $$
--   y\in\mathrm{source}(Z_i\circ X_i^{-1}),\qquad X_i^{-1}(y)\in P_i,\qquad Z_i(X_i^{-1}(y))\in Q_i .
--   $$
--
--   The global certificate components can be shrunk without changing either local chart.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CommonBranches.lean#L118-L159

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

open OAI OAI.Problem356 OAI.Problem356.CommonBranches
universe uE uM uIndex uF
open Set Metric
variable {E : Type uE} [TopologicalSpace E]
variable {M : Type uM} [PseudoMetricSpace M]

theorem OAI.Problem356.CommonBranches.exists_common_central_ball_in_components {ι : Type uIndex} [Finite ι]
    (X Z : ι → OpenPartialHomeomorph M M) (a : ι → M) (x : M)
    (haX : ∀ i, a i ∈ (X i).source) (haZ : ∀ i, a i ∈ (Z i).source)
    (hcenter : ∀ i, X i (a i) = x)
    (P Q : ι → Set M) (hP : ∀ i, IsOpen (P i)) (hQ : ∀ i, IsOpen (Q i))
    (haP : ∀ i, a i ∈ P i) (haQ : ∀ i, Z i (a i) ∈ Q i)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      ∀ i, ∀ y ∈ ball x r,
        y ∈ (outer (X i) (Z i)).source ∧
        (X i).symm y ∈ P i ∧ outer (X i) (Z i) y ∈ Q i := by sorry
