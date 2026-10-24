-- Prove2me | Theorems.Thm_K24_Global_tensorSobolevBanachRealOrders
-- name    : K24.Global.tensorSobolevBanachRealOrders
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T20:44:40.794306+00:00
-- url     : https://prove2.me/theorems/f273308a-0377-4dd4-8ce0-57f0a8c12dd5
-- title:
--   K24: exact tensor Sobolev Banach spaces at all real orders s>4
-- statement:
--   For every smooth real four-manifold M, every original bounded local cover C, every original SobolevPartition P and every real s>4, the actual symmetric native C2 tensor sections with finite P.cov2SobolevENorm s and the actual symmetric native C0 tensor sections with finite P.cov2SobolevENorm(s-2) satisfy the complete original SectionBanachSpace axioms. The carriers and extended norms are exactly tensorSobolevSpace P 2 s and tensorSobolevSpace P 0(s-2); no equivalent substitute norm is used. No compactness, Hausdorffness, auxiliary cutoff/transition bound, finite chart index or integer rounding is added.
--
--   The proof uses faithful local Sobolev representatives and exact local Bessel completeness, reconstructs genuine symmetric tensor fibers from localized coefficient limits at a nonzero partition cutoff, proves native C2/C0 regularity and chart compatibility, and proves global norm convergence by an arbitrary-index square-sum Fatou argument. It establishes both original ambient tensor Banach fields. Zero-average spaces, projection estimates, positive neighborhoods and the remaining geometric analytic conclusions remain separate obligations. This is supporting analytic infrastructure for the original K24 real-order Sobolev pair, not completion of the full mission.
--
--   Parent https://prove2.me/theorems/3db797ab-2b53-4cda-b318-e4780235e38c .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §3 equation (3.9) and §4 Banach-pair inverse transfer; exact carriers and square-sum norms are the unchanged K24GlobalAnalysis definitions.

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

theorem K24.Global.tensorSobolevBanachRealOrders :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
    [IsManifold K24.Global.I4 ∞ M]
    (C : K24.Global.BoundedLocalCover M) (P : K24.Global.SobolevPartition C)
    (s : ℝ), 4 < s →
    K24.Global.SectionBanachSpace (K24.Global.tensorSobolevSpace P 2 s)
      (P.cov2SobolevENorm s) ∧
    K24.Global.SectionBanachSpace (K24.Global.tensorSobolevSpace P 0 (s - 2))
      (P.cov2SobolevENorm (s - 2)) := by sorry
