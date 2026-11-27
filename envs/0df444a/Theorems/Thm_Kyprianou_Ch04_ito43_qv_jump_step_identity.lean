-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_jump_step_identity
-- name    : Kyprianou.Ch04.ito43_qv_jump_step_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:29:04.92937+00:00
-- url     : https://prove2.me/theorems/43e97a19-dfdb-48d0-8502-1da24498d694
-- title:
--   Jump step integral equals a finite cumulative energy difference
-- statement:
--   Apply finite-step integral linearity to the jump energy and identify each strict threshold with the cumulative energy difference.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_jump_step_identity
    (μ : Measure (ℝ × ℝ)) (t : NNReal)
    (hi : IntegrableOn (fun z : ℝ × ℝ => z.2^2/2)
      (Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)) μ)
    (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ) :
    let W : ℝ → ℝ := fun s =>
      ∑ i ∈ Finset.range m, c i * (if (b i:ℝ) < s then (1:ℝ) else 0)
    let S : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)
    IntegrableOn (fun z : ℝ × ℝ => W z.1 * (z.2^2/2)) S μ ∧
      (∫ z in S, W z.1 * (z.2^2/2) ∂μ) =
        ∑ i ∈ Finset.range m, c i *
          ((∫ z in S, z.2^2/2 ∂μ) -
           ∫ z in Icc (0:ℝ) ((min t (b i):NNReal):ℝ) ×ˢ (univ : Set ℝ),
             z.2^2/2 ∂μ) := by sorry
