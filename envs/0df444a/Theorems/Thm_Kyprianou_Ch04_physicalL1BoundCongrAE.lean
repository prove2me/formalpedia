-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalL1BoundCongrAE
-- name    : Kyprianou.Ch04.physicalL1BoundCongrAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:21:28.981802+00:00
-- url     : https://prove2.me/theorems/f549f6f9-180d-4c62-a706-c60899a5772a
-- title:
--   physicalL1BoundCongrAE
-- statement:
--   A physical L1 continuity bound implies almost-everywhere congruence.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical completion.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
set_option autoImplicit false

/-- A physical L1 bound transfers almost-everywhere equality of kernels. -/
theorem Kyprianou.Ch04.physicalL1BoundCongrAE {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) (P : Measure Omega)
    (f g : A → ℝ) (X Y : Omega → ℝ)
    (hfg : f =ᵐ[mu] g) (hX : Integrable X P) (hY : Integrable Y P)
    (hbound : (∫ w, |X w - Y w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu) :
    X =ᵐ[P] Y := by
  sorry
