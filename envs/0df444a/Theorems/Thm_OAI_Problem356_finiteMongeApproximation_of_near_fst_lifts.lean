-- Prove2me | Theorems.Thm_OAI_Problem356_finiteMongeApproximation_of_near_fst_lifts
-- name    : OAI.Problem356.finiteMongeApproximation_of_near_fst_lifts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:01:39.087398+00:00
-- url     : https://prove2.me/theorems/e0735c4c-48e4-479e-a9d5-3d24ee2f9c09
-- title:
--   Finite Monge approximation from near-diagonal lifts
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. A three-coupling of $\mu$ is a probability measure on triples with all three marginals $\mu$, and the Kantorovich value is the infimum of $\int c\,d\pi$ over three-couplings. A map $T$ preserves $\mu$ if it is measurable and $T_\#\mu=\mu$; the graph cost of $(T_2,T_3)$ is $\int c(x,T_2x,T_3x)\,d\mu(x)$. Let $\pi$ be an optimal three-coupling of a probability measure $\mu$ that is $\eta$-separated almost everywhere for some $\eta>0$. Suppose that for every $\delta>0$ there is a measurable $Q$ with $Q_\#\mu=\pi$ and $|x-(Qx)_1|\le\delta$ for $\mu$-a.e. $x$. Then for every $\varepsilon>0$ there are $\mu$-preserving maps $T_2,T_3$ with finite graph cost and
--   $$
--   \int c(x,T_2x,T_3x)\,d\mu\le\text{Kantorovich value}+\varepsilon .
--   $$
--
--   The Monge infimum equals the Kantorovich value even though it is not attained.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SeparatedLiftApproximation.lean#L12-L46

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

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.finiteMongeApproximation_of_near_fst_lifts
    {mu : Measure E3} [IsProbabilityMeasure mu] {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t)
    (hlifts : ∀ delta : ℝ, 0 < delta →
      ∃ Q : E3 → Triple, Measurable Q ∧ Measure.map Q mu = pi ∧
        ∀ᵐ x ∂mu, dist x (Q x).1 ≤ delta) :
    FiniteMongeApproximation mu := by sorry
