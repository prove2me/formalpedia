-- Prove2me | Theorems.Thm_OAI_Problem356_hasCoulombCounterexample_of_branches
-- name    : OAI.Problem356.hasCoulombCounterexample_of_branches
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:50:06.225962+00:00
-- url     : https://prove2.me/theorems/33a43690-158c-4558-a353-f825677e65bf
-- title:
--   Branch data with a contact certificate give a Coulomb counterexample
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. A three-coupling of $\mu$ is a probability measure on triples with all three marginals $\mu$; the Kantorovich value is the infimum of $\int c\,d\pi$ over three-couplings, and a Monge optimizer is a pair of $\mu$-preserving maps $(T_2,T_3)$ whose graph coupling attains it. A smooth compact probability density $\rho$ is nonnegative, smooth, compactly supported, with smooth compactly supported square root and $\int\rho=1$. For a probability measure $\nu$ and maps $H_0,\dots,H_3$, the branch marginal is $\mu=\frac13\nu+\frac16\sum_iH_{i\#}\nu$, and the branch coupling $\pi_0$ symmetrizes the two graphs $x\mapsto(x,H_0x,H_1x)$ and $x\mapsto(x,H_2x,H_3x)$ over cyclic orderings. Let $B$ be measurable with $\nu$ carried by $B$, and let the maps $H_i$ be measurable and injective on $B$, with measurable images of measurable subsets of $B$, such that $B,H_0(B),\dots,H_3(B)$ are pairwise disjoint and contained in a measurable set $U$. Assume the density measure of a smooth compact probability density $\rho$ equals $\mu$. Let $p\ge0$ be measurable with $\int p\,d\mu<\infty$ and $C<\infty$ such that:
--
--   1. for all $x,y,z\in U$,
--   $$
--   p(x)+p(y)+p(z)\le c(x,y,z)+C ;
--   $$
--   2. equality holds along both branch graphs $\nu$-a.e.;
--   3. equality with $x\in B$ and $y,z\in U$ forces $y=H_ix$ for some $i$.
--
--   Then $\rho$ is a Coulomb counterexample: the Kantorovich value of $\rho\,dx$ is finite and attained, but no pair of measure-preserving maps attains it.
--
--   This is the abstract mechanism of the counterexample: a dual certificate whose contact set splits the central mass between two branches, with incompatible weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CounterexampleAssembly.lean#L53-L130

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

theorem OAI.Problem356.hasCoulombCounterexample_of_branches
    (rho : E3 → ℝ) (hrho : IsSmoothCompactProbabilityDensity rho)
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    (hdensity : densityMeasure rho = branchMarginal nu (H 0) (H 1) (H 2) (H 3))
    {B U : Set E3} (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B → MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C)
    (hselect : ∀ x y z : E3, x ∈ B → y ∈ U → z ∈ U →
      triplePotential p (x, (y, z)) = coulombCost (x, (y, z)) + C →
      ∃ i, y = H i x) :
    HasCoulombCounterexample rho := by sorry
