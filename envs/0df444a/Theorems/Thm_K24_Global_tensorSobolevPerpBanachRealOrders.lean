-- Prove2me | Theorems.Thm_K24_Global_tensorSobolevPerpBanachRealOrders
-- name    : K24.Global.tensorSobolevPerpBanachRealOrders
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:04:18.174+00:00
-- url     : https://prove2.me/theorems/d3176fe9-3866-452f-a4d5-811b0dcc0968
-- title:
--   K24: exact zero-Haar-average tensor Sobolev Banach spaces for every real s>4
-- statement:
--   For every smooth real four-manifold, every original bounded local cover and SobolevPartition, every genuine smooth circle action rho, and every real s>4, the actual spaces tensorSobolevPerp P 2 s rho and tensorSobolevPerp P 0(s-2)rho satisfy all original SectionBanachSpace axioms for the unchanged P.cov2SobolevENorm at the corresponding real order. These carriers consist of actual symmetric native C2 or C0 sections with finite original Sobolev norm and zero canonical Haar average; they are not quotient substitutes. No compactness or Hausdorffness of the manifold, uniform action norm bound, Sobolev projection preservation, or norm-continuous orbit assumption is added.
--
--   The proof first uses a genuinely nonzero partition cutoff and the quantitative local continuous-representative theorem to bound actual tensor evaluation at each point by the original global norm. Native continuity gives genuine pointwise Haar integrability and continuous scalar action orbits. Banach–Steinhaus makes each scalar Haar evaluation a continuous linear functional on the already constructed original ambient Sobolev Banach space. Their common kernel is precisely the literal zero-Haar-average space and is closed; the original norm and all completeness laws restrict to that kernel.
--
--   This closes the original perp_domain_banach and perp_target_banach fields. It does not claim Sobolev preservation or estimates for the average itself, geometric operator bounds, Frechet differentiability or the complete K24 mission. Parent https://prove2.me/theorems/06fdeaf7-3709-47fc-b5c6-674da98954a4 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — derived zero-average Banach foundations for the common Haar framework in §1, real Sobolev pair in §3 equation (3.9), and inverse transfer in §4. Exact carriers and norms are unchanged K24GlobalAnalysis definitions.

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
universe u
noncomputable section
open scoped ContDiff Manifold ENNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16

theorem K24.Global.tensorSobolevPerpBanachRealOrders :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
    [IsManifold K24.Global.I4 ∞ M]
    (C : K24.Global.BoundedLocalCover M) (P : K24.Global.SobolevPartition C)
    (rho : K24.Global.CircleAction M) (s : ℝ), 4 < s →
    K24.Global.SectionBanachSpace (K24.Global.tensorSobolevPerp P 2 s rho)
      (P.cov2SobolevENorm s) ∧
    K24.Global.SectionBanachSpace (K24.Global.tensorSobolevPerp P 0 (s - 2) rho)
      (P.cov2SobolevENorm (s - 2)) := by sorry
