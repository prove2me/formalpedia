-- Prove2me | Theorems.Thm_K24_Global_FlatTorus_actualDefectAndMetricPositivity
-- name    : K24.Global.FlatTorus.actualDefectAndMetricPositivity
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:36:54.620992+00:00
-- url     : https://prove2.me/theorems/f3431776-927c-4ffd-b44c-dc212eda4bd8
-- title:
--   K24: actual torus Lie and Bianchi defect, with nearby metric positivity
-- statement:
--   The result concerns the actual four-torus `Fin 4 → Circle`, with the unchanged charted structure pushed forward from `q(x)_i = exp(i x_i)`. Its actual frame, flat metric, Lie derivative, and Bianchi operator are the canonical definitions in `Definitions/Def_K24GlobalStatement.lean` and its imports. The theorem has three conclusions; there are no extra geometric or analytic assumptions.
--
--   Write `f(r) = n^{-(3+alpha)} sin(n r)`, with the canonical `Real.rpow` convention, including at n = 0. For every real alpha, every natural n (including zero), and every lift x in Euclidean four-space:
--
--   1. The literal pullback coefficients of `lieTensor testVector (perturbation alpha n)` vanish except for `L_00 = cos(x_1) f'(x_0)` and `L_01 = L_10 = -sin(x_1) f(x_0)`. Lean indices 0 and 1 correspond to the source's coordinates x_1 and x_2. This is the actual reconstructed tensor, rather than a separately supplied coordinate formula.
--   2. The literal pullback of `unprojectedDefect alpha n`, which is canonically `bianchi flatMetric (lieTensor testVector (perturbation alpha n))`, equals `expectedDefectCoefficients alpha n x`. Its zeroth component is `cos(x_1) (f(x_0) - (1/2) f''(x_0))`; its first is `(1/2) sin(x_1) f'(x_0)`; the other two are zero.
--   3. For every canonical HolderExponent alpha, so `0 < alpha.value < 1`, and every natural n with `2 ≤ n`, the actual `nearbyMetric alpha.value n = flatMetric + perturbation alpha.value n` is symmetric and positive definite.
--
--   This closes the unprojected native Lie/Bianchi computation and nearby-metric positivity portions of the original torus sharpness construction. It does not establish the circle action, Haar integrability/projection identities, full section Hölder norms, the projected lower bound, or the actual vector-operator difference identity. It therefore does not complete `FlatTorus.SharpnessStatement` or the original K24 root.
--
--   Supporting original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §5.1 equations (5.6)–(5.8), the prescribed flat torus, diagonal perturbation and cosine test vector.

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

open K24.Global K24.Global.FlatTorus

theorem K24.Global.FlatTorus.actualDefectAndMetricPositivity :
  (∀ (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4),
    coverCov2 (lieTensor testVector (perturbation alpha n)) x i j =
      if i = 0 ∧ j = 0 then
        Real.cos (x 1) * deriv (liftedOscillation alpha n) (x 0)
      else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
        -Real.sin (x 1) * liftedOscillation alpha n (x 0)
      else 0) ∧
  (∀ (alpha : ℝ) (n : ℕ) (x : FourSpace),
    coverCovector (unprojectedDefect alpha n) x = expectedDefectCoefficients alpha n x) ∧
  (∀ (alpha : HolderExponent) (n : ℕ), 2 ≤ n → IsMetric (nearbyMetric alpha.value n)) := by sorry
