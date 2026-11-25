-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42GridCoefficientAELimitV1
-- name    : Kyprianou.Ch04.exercise42GridCoefficientAELimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T10:12:03.224852+00:00
-- url     : https://prove2.me/theorems/45884d48-a065-4764-b064-906720dafdf1
-- title:
--   Almost-everywhere convergence of first partial derivative at floor grid samples
-- statement:
--   The countable cadlag discontinuities and zero are null. Uniform floor samples converge, and positivity puts the first coordinate in the interior where the full derivative is continuous.
-- source:
--   Kyprianou (2006), Exercise 4.2; deterministic Stieltjes grid proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42GridCoefficientAELimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hd : 0 < c) (hzero : X 0 omega = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hNeg : ∀ t : NNReal, 0 < t → X t omega ≤ Xleft t omega)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (U : NNReal → Real) (K : NNReal) (hU : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))

    (t : NNReal) (ht : 0 < t) :
    let T : ℝ := t
    ∀ᵐ s ∂(volume.restrict (Icc 0 T)),
      Tendsto (fun n : ℕ => (fun s : NNReal => fderiv ℝ f (U s, X s omega) (1, 0)) (T * (⌊(s / T) * ((n : ℝ) + 2)⌋₊ : ℝ) / ((n : ℝ) + 2)).toNNReal) atTop (nhds ((fun s : NNReal => fderiv ℝ f (U s, X s omega) (1, 0)) s.toNNReal)) := by
  sorry
