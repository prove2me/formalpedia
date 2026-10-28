-- Prove2me | Theorems.Thm_K24_Global_exactSobolevHaarProjections
-- name    : K24.Global.exactSobolevHaarProjections
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:20:43.597597+00:00
-- url     : https://prove2.me/theorems/f7442f98-a680-4c6a-a413-5840acc4e74c
-- title:
--   K24: exact Haar projection estimates for all real Sobolev orders s>4
-- statement:
--   For every smooth four-manifold and the original bounded cover and SobolevPartition, every real s>4, H>=0 and genuine circle action satisfying the original SobolevActionControl P s H, the actual Haar averages and complements preserve each original tensor and covector Sobolev class of native order 2-j and real order s-j for j=0,1,2. The conclusion gives actual coordinate Haar integrability, tensor-average idempotence, zero Haar average of each complement, and the exact original norm bounds H and 1+H without covering-degree or component-count factors. IsNonzero means zero Haar average and permits the zero section. No finite chart index, norm-continuous orbit hypothesis, replacement norm or integer-only assumption is added. The proof establishes measurability of actual local Bessel L2 representatives, identifies their integral with the genuine scalar Haar average, controls finite Hilbert products and passes over arbitrary-index finite partial sums, then recovers genuine native C(2-j) representatives from the real-order local theorem. These are exactly the two original projection fields, not completion of the remaining operator estimates or nonlinear analytic core. Parent https://prove2.me/theorems/06fdeaf7-3709-47fc-b5c6-674da98954a4 .
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

open K24.Global in
theorem K24.Global.exactSobolevHaarProjections {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] {C : BoundedLocalCover M} (P : SobolevPartition C)
    (s : ℝ) (hs : 4 < s) (H : ℝ≥0) (rho : CircleAction M)
    (hcontrol : SobolevActionControl P s H rho) :
    (∀ j ≤ 2, ∀ u : RawCov2 M, P.Cov2Sobolev (2 - j) (s - j) u →
      Cov2HaarIntegrable rho u ∧
      P.Cov2Sobolev (2 - j) (s - j) (cov2Pi0 rho u) ∧
      P.Cov2Sobolev (2 - j) (s - j) (cov2PiPerp rho u) ∧
      cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
      IsNonzeroCov2 rho (cov2PiPerp rho u) ∧
      P.cov2SobolevENorm (s - j) (cov2Pi0 rho u) ≤
        (H : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u ∧
      P.cov2SobolevENorm (s - j) (cov2PiPerp rho u) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u) ∧
    (∀ j ≤ 2, ∀ eta : RawCovector M, P.CovectorSobolev (2 - j) (s - j) eta →
      CovectorHaarIntegrable rho eta ∧
      P.CovectorSobolev (2 - j) (s - j) (covectorPi0 rho eta) ∧
      P.CovectorSobolev (2 - j) (s - j) (covectorPiPerp rho eta) ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta) ∧
      P.covectorSobolevENorm (s - j) (covectorPi0 rho eta) ≤
        (H : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta ∧
      P.covectorSobolevENorm (s - j) (covectorPiPerp rho eta) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta) := by sorry
