-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ce_bad_first_grid
-- name    : Kyprianou.Ch04.ito43_ce_bad_first_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:10:26.186713+00:00
-- url     : https://prove2.me/theorems/f155bb7b-b370-46fd-ab0d-70c51b6fc948
-- title:
--   Arbitrary initial left value prevents stopped spatial grid error convergence
-- statement:
--   For deterministic unit drift and a quadratic test function, an arbitrary unbounded initial left value produces a stopped first-cell error at least one.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3 formalisation boundary audit.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The erroneous initial left value gives a nonvanishing stopped first-cell remainder. -/

theorem Kyprianou.Ch04.ito43_ce_bad_first_grid (n : ℕ) (hn : 0 < n) :
    let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
    let Y : NNReal → ℕ → ℝ := fun t w => if t = 0 then (w : ℝ) else (t : ℝ)
    let f : ℝ × ℝ → ℝ := fun z => z.2 ^ 2
    let t : NNReal := 1 / (n : NNReal)
    let u : ℕ → NNReal := fun k => (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    t ≤ 1 ∧ 1 ≤ |∑ k ∈ Finset.range n,
      (f ((v k : ℝ), X (v (k+1)) n) - f ((v k : ℝ), X (v k) n) -
        fderiv ℝ f ((u k : ℝ),Y (u k) n) (0,1) *
          (X (v (k+1)) n - X (v k) n))| := by sorry
