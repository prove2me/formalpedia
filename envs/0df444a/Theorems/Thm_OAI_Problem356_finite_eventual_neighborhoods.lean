-- Prove2me | Theorems.Thm_OAI_Problem356_finite_eventual_neighborhoods
-- name    : OAI.Problem356.finite_eventual_neighborhoods
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:59:55.310474+00:00
-- url     : https://prove2.me/theorems/0304db9e-8423-4c7d-89cd-53aa79417874
-- title:
--   A common radius for finitely many local properties
-- statement:
--   Let $s$ be a finite index set, $p_i$ points of a pseudometric space and $P_i$ properties with $P_i(x)$ for all $x$ near $p_i$ ($i\in s$). Then there is $r>0$ such that
--   $$
--   d(x,p_i)<r\implies P_i(x)\qquad\text{for all }i\in s .
--   $$
--
--   A single radius serves all finitely many centers. This lets the five components be chosen as balls of one size.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CertificateNeighborhoods.lean#L14-L36

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

open OAI OAI.Problem356
universe uIndex uX uY
open Set Filter Metric
open scoped ENNReal

theorem OAI.Problem356.finite_eventual_neighborhoods {ι : Type uIndex} {X : Type uX} [PseudoMetricSpace X]
    (s : Finset ι) (p : ι → X) (P : ι → X → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ x in nhds (p i), P i x) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r → P i x := by sorry
