-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42GridCellIntegralV1
-- name    : Kyprianou.Ch04.exercise42GridCellIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T09:54:20.78925+00:00
-- url     : https://prove2.me/theorems/6abc9ec1-aa14-52c9-8e32-b58aa8062146
-- title:
--   Exact finite left-grid sum as derivative-weighted integral
-- statement:
--   The natural floor index selects its grid cell; integrate the constant coefficient times the derivative using the absolutely continuous FTC, then sum adjacent intervals.
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

theorem Kyprianou.Ch04.exercise42GridCellIntegralV1
    (t : NNReal) (ht : 0 < t) (U g : NNReal → ℝ)
    (K : NNReal) (hU : LipschitzWith K U)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ s : NNReal, s ≤ t → ‖g s‖ ≤ C) :
    let T : ℝ := t
    let V : ℝ → ℝ := fun s => U s.toNNReal
    let D : ℝ → ℝ := deriv V
    let q : ℕ → ℕ → ℝ := fun n i => T * (i : ℝ) / ((n : ℝ) + 2)
    let j : ℕ → ℝ → ℕ := fun n s => ⌊(s / T) * ((n : ℝ) + 2)⌋₊
    let F : ℕ → ℝ → ℝ := fun n s => g (q n (j n s)).toNNReal * D s
    ∀ n : ℕ,
      (∫ s in Icc 0 T, F n s) =
        ∑ i ∈ Finset.range (n + 2),
          g (t * (i : NNReal) / ((n + 2 : ℕ) : NNReal)) *
            (U (t * ((i + 1 : ℕ) : NNReal) / ((n + 2 : ℕ) : NNReal)) -
             U (t * (i : NNReal) / ((n + 2 : ℕ) : NNReal))) := by
  sorry
