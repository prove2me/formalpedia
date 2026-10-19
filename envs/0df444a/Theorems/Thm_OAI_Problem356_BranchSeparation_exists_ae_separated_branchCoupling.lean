-- Prove2me | Theorems.Thm_OAI_Problem356_BranchSeparation_exists_ae_separated_branchCoupling
-- name    : OAI.Problem356.BranchSeparation.exists_ae_separated_branchCoupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:43:45.434982+00:00
-- url     : https://prove2.me/theorems/9d965600-9f67-4276-922c-0384a077bade
-- title:
--   The branch coupling is uniformly separated
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. A three-coupling of $\mu$ is a probability measure on triples with all three marginals $\mu$; the Kantorovich value is the infimum of $\int c\,d\pi$ over three-couplings, and a Monge optimizer is a pair of $\mu$-preserving maps $(T_2,T_3)$ whose graph coupling attains it. A smooth compact probability density $\rho$ is nonnegative, smooth, compactly supported, with smooth compactly supported square root and $\int\rho=1$. For a probability measure $\nu$ and maps $H_0,\dots,H_3$, the branch marginal is $\mu=\frac13\nu+\frac16\sum_iH_{i\#}\nu$, and the branch coupling $\pi_0$ symmetrizes the two graphs $x\mapsto(x,H_0x,H_1x)$ and $x\mapsto(x,H_2x,H_3x)$ over cyclic orderings. Suppose $\nu$ is carried by a compact set $K$, each $H_i$ is measurable and continuous on $K$, and the five sets $K,H_0(K),\dots,H_3(K)$ are pairwise disjoint. Then there is $\eta>0$ such that $\pi_0$-almost every triple is $\eta$-separated:
--   $$
--   |x-y|,\ |x-z|,\ |y-z|\ \ge\ \eta .
--   $$
--
--   In particular the coupling has bounded Coulomb cost. This gives finiteness of the Kantorovich value.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/BranchSeparation.lean#L35-L61

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation

open OAI OAI.Problem356 OAI.Problem356.BranchSeparation
open MeasureTheory Set
open scoped ENNReal

theorem OAI.Problem356.BranchSeparation.exists_ae_separated_branchCoupling
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t := by sorry
