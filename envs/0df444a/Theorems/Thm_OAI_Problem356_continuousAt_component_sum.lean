-- Prove2me | Theorems.Thm_OAI_Problem356_continuousAt_component_sum
-- name    : OAI.Problem356.continuousAt_component_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:02:40.510482+00:00
-- url     : https://prove2.me/theorems/ccd2f119-4041-4815-938e-a278363117eb
-- title:
--   Continuity of the potential sum of a component type
-- statement:
--   Let $p_i$ be points of $\mathbb{R}^3$ and $v_i$ real potentials continuous at $p_i$. For an ordered type $(i,j,k)$, the function on triples
--   $$
--   (x,y,z)\mapsto\bigl(v_i(x)+v_j(y)+v_k(z)\bigr)^+\in[0,\infty)
--   $$
--   is continuous at $(p_i,p_j,p_k)$.
--
--   This lets strict inequalities at the centers propagate to neighborhoods.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/ComponentCertificate.lean#L49-L66

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

open OAI OAI.Problem356
universe uIndex
open Set Filter Metric
open scoped ENNReal BigOperators

theorem OAI.Problem356.continuousAt_component_sum {ι : Type uIndex} (p : ι → E3) (v : ι → E3 → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) (a : ι × (ι × ι)) :
    ContinuousAt
      (fun t : Triple => ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2))
      (p a.1, (p a.2.1, p a.2.2)) := by sorry
