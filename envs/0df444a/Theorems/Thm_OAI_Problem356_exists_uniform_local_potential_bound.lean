-- Prove2me | Theorems.Thm_OAI_Problem356_exists_uniform_local_potential_bound
-- name    : OAI.Problem356.exists_uniform_local_potential_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:25:40.354277+00:00
-- url     : https://prove2.me/theorems/b6488862-1176-45a8-9931-0117b06e1af8
-- title:
--   Uniform bounds for finitely many potentials near their centers
-- statement:
--   Let $p_i$ ($i$ finite) be points of a pseudometric space and $v_i$ real functions continuous at $p_i$. Then there are $M>0$ and $r>0$ with
--   $$
--   |v_i(x)|\le M\qquad\text{whenever }d(x,p_i)<r .
--   $$
--
--   The glued supporting potential is bounded on the component balls, as required for the shifted certificate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalPotentialBounds.lean#L12-L34

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

open OAI OAI.Problem356
universe uIndex uX
open Set Filter Metric
open scoped BigOperators

theorem OAI.Problem356.exists_uniform_local_potential_bound {ι : Type uIndex} {X : Type uX} [Fintype ι]
    [PseudoMetricSpace X] (p : ι → X) (v : ι → X → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) :
    ∃ M : ℝ, 0 < M ∧ ∃ r : ℝ, 0 < r ∧
      ∀ i x, x ∈ ball (p i) r → |v i x| ≤ M := by sorry
