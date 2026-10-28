-- Prove2me | Theorems.Thm_K24_Global_originalFractionalSobolevPullback
-- name    : K24.Global.originalFractionalSobolevPullback
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T05:21:39.130178+00:00
-- url     : https://prove2.me/theorems/f0af4c30-1f52-4cac-97af-009bfde3697b
-- title:
--   K24: nonlinear pullback for all representatives in the original fractional Bessel Sobolev space
-- statement:
--   For every real $0<\alpha<1$ and finite nonnegative constants $J,L$, there is a finite $B=B(\alpha,J,L)$ with the following property. Let $\varphi:\mathbb R^4\to\mathbb R^4$ be everywhere differentiable and injective, with derivative $D\varphi$, such that $1\le J|\det D\varphi(x)|$ for every $x$ and $\|\varphi(x)-\varphi(y)\|\le L\|x-y\|$ for all $x,y$. Every real function $f$ in the original inhomogeneous Bessel Sobolev space $H^\alpha(\mathbb R^4)$ then has $f\circ\varphi\in H^\alpha(\mathbb R^4)$ and $$\|f\circ\varphi\|_{H^\alpha}\le B\|f\|_{H^\alpha}.$$ The norm is exactly the fixed K24 Fourier-Bessel norm. No continuity of the chosen representative is assumed; the map hypotheses ensure that pullback preserves almost-everywhere equality. This supplies the fractional-order ingredient for coordinate pullback estimates. It is conditional on the displayed global map hypotheses; deriving localized atlas versions and higher-order estimates remains separate.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — derived real-order coordinate-pullback foundation for the Sobolev estimates in §3; exact K24 canonical Bessel norms are retained.

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

open MeasureTheory K24.Global

theorem K24.Global.originalFractionalSobolevPullback
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (J L : ℝ≥0) :
    ∃ B : ℝ≥0, ∀ (φ : FourSpace → FourSpace)
      (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace),
      (∀ x, HasFDerivAt φ (Dφ x) x) → Function.Injective φ →
      (∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|) →
      (∀ x y, ‖φ x-φ y‖ ≤ (L : ℝ) * ‖x-y‖) →
      ∀ f : FourSpace → ℝ, LocalSobolevMem α f →
        LocalSobolevMem α (f ∘ φ) ∧
          localSobolevENN α (f ∘ φ) ≤ (B : ℝ≥0∞) * localSobolevENN α f := by sorry
