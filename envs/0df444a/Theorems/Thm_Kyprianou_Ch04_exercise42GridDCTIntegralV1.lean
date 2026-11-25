-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42GridDCTIntegralV1
-- name    : Kyprianou.Ch04.exercise42GridDCTIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T09:55:16.714685+00:00
-- url     : https://prove2.me/theorems/14c0383e-9372-4345-9e88-8f088aa80ad9
-- title:
--   Dominated convergence of derivative-weighted grid integrals
-- statement:
--   Measurable floor indices and derivative, compact coefficient bound and Lipschitz derivative norm bound give the integrable constant majorant. Multiply the supplied AE coefficient limit by the fixed derivative and apply DCT.
-- source:
--   Kyprianou (2006), Exercise 4.2; deterministic Stieltjes grid proof.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise42GridDCTIntegralV1
    (t : NNReal) (ht : 0 < t) (U g : NNReal → ℝ)
    (K : NNReal) (hU : LipschitzWith K U)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ s : NNReal, s ≤ t → ‖g s‖ ≤ C)
    (hpoint : ∀ᵐ s ∂(volume.restrict (Icc 0 (t : ℝ))),
      Tendsto (fun n : ℕ => g (((t : ℝ) *
        (⌊(s / (t : ℝ)) * ((n : ℝ) + 2)⌋₊ : ℝ)) /
        ((n : ℝ) + 2)).toNNReal) atTop (nhds (g s.toNNReal))) :
    let T : ℝ := t
    let V : ℝ → ℝ := fun s => U s.toNNReal
    let D : ℝ → ℝ := deriv V
    let q : ℕ → ℕ → ℝ := fun n i => T * (i : ℝ) / ((n : ℝ) + 2)
    let j : ℕ → ℝ → ℕ := fun n s => ⌊(s / T) * ((n : ℝ) + 2)⌋₊
    let F : ℕ → ℝ → ℝ := fun n s => g (q n (j n s)).toNNReal * D s
    Tendsto (fun n => ∫ s in Icc 0 T, F n s) atTop
      (nhds (∫ s in Icc 0 T, g s.toNNReal * D s)) := by
  sorry
