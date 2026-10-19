-- Prove2me | Theorems.Thm_OAI_Problem356_branchCoupling_optimality_of_shifted_certificate
-- name    : OAI.Problem356.branchCoupling_optimality_of_shifted_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:51:22.421745+00:00
-- url     : https://prove2.me/theorems/5397f2ac-3379-4153-8686-c98a0c4ef841
-- title:
--   The branch coupling is optimal under a contact certificate
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. A three-coupling of $\mu$ is a probability measure on triples with all three marginals $\mu$, and the Kantorovich value is the infimum of $\int c\,d\pi$ over three-couplings. For a probability measure $\nu$ and measurable maps $H_0,\dots,H_3$, let $\mu=\frac13\nu+\frac16\sum_iH_{i\#}\nu$ be the branch marginal and $\pi_0$ the branch coupling, which symmetrizes the graphs $x\mapsto(x,H_0x,H_1x)$ and $x\mapsto(x,H_2x,H_3x)$ over cyclic orderings. Let $U$ be measurable and carry $\mu$, and let $p\ge0$ be measurable with $\int p\,d\mu<\infty$ and $C<\infty$, such that $p(x)+p(y)+p(z)\le c(x,y,z)+C$ on $U^3$ and equality holds along both branch graphs $\nu$-a.e. Then
--   $$
--   \int c\,d\pi_0=\text{Kantorovich value of }\mu<\infty .
--   $$
--
--   The explicit coupling itself is the optimizer, not merely some optimizer. Its geometric separation is then available for the Monge approximation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/BranchOptimizer.lean#L23-L55

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

theorem OAI.Problem356.branchCoupling_optimality_of_shifted_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {U : Set E3} (hU : MeasurableSet U)
    (hmuU : ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
        kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
      (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by sorry
