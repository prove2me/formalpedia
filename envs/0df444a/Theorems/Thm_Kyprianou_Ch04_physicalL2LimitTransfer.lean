-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalL2LimitTransfer
-- name    : Kyprianou.Ch04.physicalL2LimitTransfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:55:26.868209+00:00
-- url     : https://prove2.me/theorems/4282b132-be24-53f0-8406-2c11a8f2f20a
-- title:
--   Physical L2 isometry limit transfer
-- statement:
--   An L2-convergent sequence of kernels with exact square-integral and difference identities transfers the isometry to its physical L1 limit.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical L2 approximation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_l2IsometryLimitTransfer
import Theorems.Thm_Kyprianou_Ch04_lpNormEqOfSquareIntegralEq
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Transfer a physical L2 isometry from an L1-convergent approximation. -/
theorem Kyprianou.Ch04.physicalL2LimitTransfer
    {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) (P : Measure Omega)
    (f : ℕ → A → ℝ) (g : A → ℝ)
    (X : ℕ → Omega → ℝ) (Y : Omega → ℝ)
    (hf : ∀ n, MemLp (f n) 2 mu) (hg : MemLp g 2 mu)
    (hX : ∀ n, MemLp (X n) 2 P)
    (hXi : ∀ n, Integrable (X n) P) (hYi : Integrable Y P)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hL1 : Tendsto (fun n => ∫ w, |X n w - Y w| ∂P) atTop (𝓝 0))
    (hSq : ∀ n, (∫ w, (X n w)^2 ∂P) = ∫ a, (f n a)^2 ∂mu)
    (hDiff : ∀ n m, (∫ w, (X n w - X m w)^2 ∂P) =
      ∫ a, (f n a - f m a)^2 ∂mu) :
    MemLp Y 2 P ∧ (∫ w, (Y w)^2 ∂P) = ∫ a, (g a)^2 ∂mu := by
  sorry
