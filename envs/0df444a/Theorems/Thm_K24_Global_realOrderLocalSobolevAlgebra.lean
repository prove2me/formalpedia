-- Prove2me | Theorems.Thm_K24_Global_realOrderLocalSobolevAlgebra
-- name    : K24.Global.realOrderLocalSobolevAlgebra
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:37:36.307035+00:00
-- url     : https://prove2.me/theorems/034cfec6-9a8d-4105-bafd-60ffa76ca6ee
-- title:
--   K24: product estimate in the original real-order Bessel norm
-- statement:
--   For every real r>2 there exists a finite nonnegative constant A, depending only on r, such that any real functions f,g on the original Euclidean four-dimensional coefficient model with LocalSobolevMem r have a pointwise product in the same original class and localSobolevENN r(f*g) <= A*localSobolevENN r f*localSobolevENN r g. These functions are measured globally on the Euclidean model; local in the name refers to their role as localized chart coefficients. No continuity assumption is added, and all real exponents are retained. The proof constructs faithful bounded continuous representatives through the accepted Fourier L1 bound, proves an actual weighted convolution estimate using the exact Bessel weights and Young L1*L2 control, identifies inverse Fourier convolution with physical multiplication, and descends back to the actual a.e. representatives with exactly the original norm. This theorem proves multiplication closure and an estimate, not all original manifold operator estimates or the full analytic core. Parent https://prove2.me/theorems/06fdeaf7-3709-47fc-b5c6-674da98954a4 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — derived real-order coefficient foundations for §3 equation (3.9); exact unchanged K24GlobalAnalysis local Sobolev definitions and pinned Mathlib Fourier/Bessel normalization.

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

theorem K24.Global.realOrderLocalSobolevAlgebra :
  ∀ (r : ℝ), 2 < r → ∃ A : ℝ≥0,
    ∀ f g : K24.Global.SobolevModel → ℝ,
      K24.Global.LocalSobolevMem r f → K24.Global.LocalSobolevMem r g →
      K24.Global.LocalSobolevMem r (f * g) ∧
        K24.Global.localSobolevENN r (f * g) ≤
          (A : ℝ≥0∞) * K24.Global.localSobolevENN r f * K24.Global.localSobolevENN r g := by sorry
