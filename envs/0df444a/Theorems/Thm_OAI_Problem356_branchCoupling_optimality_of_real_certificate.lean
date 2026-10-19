-- Prove2me | Theorems.Thm_OAI_Problem356_branchCoupling_optimality_of_real_certificate
-- name    : OAI.Problem356.branchCoupling_optimality_of_real_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:52:09.038662+00:00
-- url     : https://prove2.me/theorems/356a93db-b571-48d5-92f7-2c45073cde9f
-- title:
--   Optimality of the branch coupling from a bounded real potential
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. A three-coupling of $\mu$ is a probability measure on triples with all three marginals $\mu$, and the Kantorovich value is the infimum of $\int c\,d\pi$ over three-couplings. For a probability measure $\nu$ and measurable maps $H_0,\dots,H_3$, let $\mu=\frac13\nu+\frac16\sum_iH_{i\#}\nu$ be the branch marginal and $\pi_0$ the branch coupling, which symmetrizes the graphs $x\mapsto(x,H_0x,H_1x)$ and $x\mapsto(x,H_2x,H_3x)$ over cyclic orderings. Let $\nu$ be carried by $B$, and $U$ measurable with $B\subseteq U$ and $H_i(B)\subseteq U$. Let $u$ be a measurable real potential with $|u|\le M$ on $U$, such that
--   $$
--   u(x)+u(y)+u(z)\le c(x,y,z)\quad\text{on }U^3,
--   $$
--   with equality along both branch graphs $\nu$-a.e. Then $\int c\,d\pi_0$ equals the Kantorovich value of $\mu$ and is finite.
--
--   No density, injectivity or nonattainment hypothesis is needed for this half.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/BranchOptimizer.lean#L57-L101

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

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.branchCoupling_optimality_of_real_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {B U : Set E3} (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 0 x) + u (H 1 x)) = coulombCost (x, (H 0 x, H 1 x)))
    (hcontact23 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 2 x) + u (H 3 x)) = coulombCost (x, (H 2 x, H 3 x))) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
        kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
      (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by sorry
