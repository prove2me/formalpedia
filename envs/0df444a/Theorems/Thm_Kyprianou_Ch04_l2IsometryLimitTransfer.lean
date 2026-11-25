-- Prove2me | Theorems.Thm_Kyprianou_Ch04_l2IsometryLimitTransfer
-- name    : Kyprianou.Ch04.l2IsometryLimitTransfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:49:38.11844+00:00
-- url     : https://prove2.me/theorems/27da7fc2-9a3c-41b1-b2d2-69707cfaa730
-- title:
--   Transfer the second moment isometry along a limit in measure
-- statement:
--   If input functions converge in L2 and corresponding output random variables preserve norms and pairwise L2 distances and converge in measure, the output limit is square-integrable and has exactly the input limit second moment.
-- source:
--   Completeness and continuity of L2; Kyprianou Chapter 4 Exercise 4.4 approximation argument.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_l2CauchyLimitIdentification
import Theorems.Thm_Kyprianou_Ch04_lpNormSqIntegral
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.l2IsometryLimitTransfer
    {A : Type u} {Ω : Type v} [MeasurableSpace A] [MeasurableSpace Ω]
    (μ : Measure A) (P : Measure Ω)
    (f : ℕ → A → ℝ) (g : A → ℝ)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hX : ∀ n, MemLp (X n) 2 P)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hY : TendstoInMeasure P X atTop Y)
    (hDist : ∀ n m, dist ((hX n).toLp (X n)) ((hX m).toLp (X m)) =
      dist ((hf n).toLp (f n)) ((hf m).toLp (f m)))
    (hNorm : ∀ n, ‖(hX n).toLp (X n)‖ = ‖(hf n).toLp (f n)‖) :
    MemLp Y 2 P ∧ (∫ ω, (Y ω) ^ 2 ∂P) = ∫ a, (g a) ^ 2 ∂μ := by
  sorry
