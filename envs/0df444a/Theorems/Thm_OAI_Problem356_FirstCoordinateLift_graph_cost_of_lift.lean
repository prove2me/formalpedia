-- Prove2me | Theorems.Thm_OAI_Problem356_FirstCoordinateLift_graph_cost_of_lift
-- name    : OAI.Problem356.FirstCoordinateLift.graph_cost_of_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:01:02.389434+00:00
-- url     : https://prove2.me/theorems/b291a2c0-eb9c-4ff5-a053-b4f1e9ecf5d2
-- title:
--   Graph cost of a near-diagonal lift of a separated coupling
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. A three-coupling of $\mu$ is a probability measure on triples with all three marginals $\mu$, and the Kantorovich value is the infimum of $\int c\,d\pi$ over three-couplings. A map $T$ preserves $\mu$ if it is measurable and $T_\#\mu=\mu$; the graph cost of $(T_2,T_3)$ is $\int c(x,T_2x,T_3x)\,d\mu(x)$. Let $\pi$ be a three-coupling of a probability measure $\mu$, $Q$ measurable with $Q_\#\mu=\pi$, $\eta>0$ and $\delta\le\eta/2$. Assume $\pi$-a.e. triple is $\eta$-separated and $|x-(Qx)_1|\le\delta$ for $\mu$-a.e. $x$. Then $T_2=(Q\cdot)_2$ and $T_3=(Q\cdot)_3$ preserve $\mu$, their graph cost is finite, and
--   $$
--   \int c(x,T_2x,T_3x)\,d\mu\le\int c\,d\pi+\frac{24\delta}{\eta^2} .
--   $$
--
--   Replacing the first coordinate of a coupling by the identity costs little when the coupling is separated.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/FirstCoordinateLift.lean#L47-L83

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
open CoulombEstimates

theorem OAI.Problem356.FirstCoordinateLift.graph_cost_of_lift {μ : Measure E3} [IsProbabilityMeasure μ]
    {π : Measure Triple} (hπ : IsThreeCoupling μ π)
    {Q : E3 → Triple} (hQ : Measurable Q) (hmap : Measure.map Q μ = π)
    {η δ : ℝ} (hη : 0 < η) (hδ : δ ≤ η / 2)
    (hsep : ∀ᵐ t ∂π, Separated η t)
    (hclose : ∀ᵐ x ∂μ, dist x (Q x).1 ≤ δ) :
    Preserves μ (tripleSnd ∘ Q) ∧ Preserves μ (tripleThd ∘ Q) ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) < ⊤ ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) ≤
        (∫⁻ t, coulombCost t ∂π) + ENNReal.ofReal (24 * δ / η ^ 2) := by sorry
