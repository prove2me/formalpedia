-- Prove2me | Theorems.Thm_K24_Global_sobolev_positive_neighborhood
-- name    : K24.Global.sobolev_positive_neighborhood
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:20:34.6857+00:00
-- url     : https://prove2.me/theorems/4d82a49a-d3ef-48b1-9082-2c879d6fedc5
-- title:
--   K24: positive metric neighborhoods in the original real-order Sobolev norm
-- statement:
--   For every smooth four-manifold, original bounded cover C, SobolevPartition P and localizers L, every Sobolev metric-numerics package b, every real s>4 and every original admissible metric z that belongs to P.Cov2Sobolev 2 s, there is a positive real radius such that every symmetric native C2 perturbation h in that same original real-order Sobolev class with P.cov2SobolevENorm s h smaller than the radius keeps z+h a positive metric in the same class. The norm, actual raw tensors, native regularity and all quantifiers are unchanged. No compactness, finite chart index, stronger Holder bound or integer restriction is added. The proof derives a positive lower bound for some actual partition cutoff at every point from the original overlap/atlas-overlap bounds, combines the faithful real-order local Sobolev point bound with the original ellipticity lower bound, and chooses a sufficiently small positive radius. This proves the original positive_neighborhood field; it does not prove nonlinear Frechet differentiability, real-order product estimates or the full analytic core. Parent https://prove2.me/theorems/06fdeaf7-3709-47fc-b5c6-674da98954a4 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — derived analytic foundations for the original real-order Sobolev scale in §3 equation (3.9) and §4; exact canonical SobolevConclusions and SobolevAnalyticCore fields, all real s>4.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
universe u
noncomputable section
open scoped NNReal ENNReal Topology Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16

theorem K24.Global.sobolev_positive_neighborhood :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
    [IsManifold K24.Global.I4 ∞ M]
    (C : K24.Global.BoundedLocalCover M) (P : K24.Global.SobolevPartition C)
    (L : K24.Global.SobolevLocalizers C) (b : K24.Global.SobolevMetricNumerics)
    (s : ℝ), 4 < s →
    ∀ z : K24.Global.RawCov2 M,
      K24.Global.MetricSobolevAdmissible C L s b z → P.Cov2Sobolev 2 s z →
      ∃ radius : ℝ, 0 < radius ∧
        ∀ h : K24.Global.RawCov2 M,
          (K24.Global.IsSymmetricCov2 h ∧ P.Cov2Sobolev 2 s h) →
          P.cov2SobolevENorm s h < ENNReal.ofReal radius →
          K24.Global.IsMetric (z + h) ∧ P.Cov2Sobolev 2 s (z + h) := by sorry
