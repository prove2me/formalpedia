-- Prove2me | Theorems.Thm_K24_Global_FlatTorus_geometryAndCoverCoefficients
-- name    : K24.Global.FlatTorus.geometryAndCoverCoefficients
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:20:15.536729+00:00
-- url     : https://prove2.me/theorems/ba044309-94fb-4b9d-9913-964ed2393b12
-- title:
--   K24: genuine flat-torus geometry and the prescribed cover coefficients
-- statement:
--   The theorem concerns exactly the canonical torus `Torus = Fin 4 → Circle`,
--   the prescribed periodic map `quotientMap x i = Circle.exp (x i)`, and the
--   canonical `torusChartedSpace` obtained by pushing forward local inverses of
--   this map using the chosen `arg` representative. It has no additional
--   smoothness, frame, metric, or compatibility hypotheses.
--
--   It proves the following conjunction.
--
--   1. This canonical atlas is a smooth manifold structure with model `I4`.
--   2. The actual quotient map is smooth. At every `x : FourSpace`, there is an
--      open partial homeomorphism with source containing x, whose forward function
--      is exactly `quotientMap` on its entire domain, and whose forward and inverse
--      functions are smooth on their respective source and target sets.
--   3. At every x, the quotient map has genuine manifold derivative equal to the
--      identity continuous linear map in the canonical tangent coordinates.
--      Therefore the prescribed `coverDifferential x` is that identity and is
--      invertible.
--   4. For every lift x and every basis index i, `frame (quotientMap x) i` equals
--      `coverDifferential x (basisVector i)`. For every vector v, applying
--      `coframe (quotientMap x) i` to `coverDifferential x v` gives `v i`.
--      These identities apply to every lift, independently of the chosen global
--      representative. At every torus point the frame and coframe are dual:
--      `coframe p i (frame p j) = 1` if i=j and zero otherwise.
--   5. The actual `flatMetric` is symmetric and positive definite.
--   6. For every x, its literal cover coefficient matrix is the identity:
--      `coverCov2 flatMetric x = 1`.
--   7. For every real α, every natural n, every x and indices i,j, the literal
--      cover coefficient of `perturbation α n` is
--      `liftedOscillation α n (x 0)` when i=j=0, and zero otherwise.
--   8. For every x, the literal pulled-back test vector is
--      `coverVector testVector x = cos(x 1) • basisVector 0`.
--
--   The indices 0 and 1 correspond to the mathematical coordinates x₁ and x₂.
--   The coefficient statement permits every real α and every natural n, including
--   zero; it does not assume a Hölder exponent or assert a norm bound.
--
--   This proves the geometric atlas and frame bridge for the prescribed example.
--   The theorem does not yet prove smoothness of the circle action, metric
--   invariance under it, the Haar or zero-average assertions, uniform full
--   FourSpace section norm estimates, positivity of the nearby metrics, or the
--   identity and lower bound for the actual geometric projected operator defect.
--   Those are further obligations in the original `SharpnessStatement`; the
--   original four-conjunct root is not proved by this result.
--
--   Supporting the original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §5.1 equations (5.6)–(5.8), the prescribed flat torus, diagonal perturbation and cosine test vector.

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

open K24.Global K24.Global.FlatTorus

theorem K24.Global.FlatTorus.geometryAndCoverCoefficients :
  IsManifold I4 ∞ Torus ∧
  ContMDiff I4 I4 ∞ quotientMap ∧
  (∀ x : FourSpace, ∃ e : OpenPartialHomeomorph FourSpace Torus,
    x ∈ e.source ∧ (⇑e = quotientMap) ∧
    ContMDiffOn I4 I4 ∞ e e.source ∧ ContMDiffOn I4 I4 ∞ e.symm e.target) ∧
  (∀ x : FourSpace,
    HasMFDerivAt I4 I4 quotientMap x (ContinuousLinearMap.id ℝ FourSpace) ∧
    coverDifferential x = ContinuousLinearMap.id ℝ FourSpace ∧
    (coverDifferential x).IsInvertible) ∧
  (∀ (x : FourSpace) (i : Fin 4),
    frame (quotientMap x) i = coverDifferential x (basisVector i)) ∧
  (∀ (x v : FourSpace) (i : Fin 4),
    coframe (quotientMap x) i (coverDifferential x v) = v i) ∧
  (∀ (p : Torus) (i j : Fin 4),
    coframe p i (frame p j) = if i = j then 1 else 0) ∧
  IsMetric flatMetric ∧
  (∀ x : FourSpace, coverCov2 flatMetric x = 1) ∧
  (∀ (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4),
    coverCov2 (perturbation alpha n) x i j =
      if i = 0 ∧ j = 0 then liftedOscillation alpha n (x 0) else 0) ∧
  (∀ x : FourSpace, coverVector testVector x = Real.cos (x 1) • basisVector 0) := by sorry
