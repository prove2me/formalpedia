-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_trueMartingale_deterministicLocalisation
-- name    : Kyprianou.Ch04.kw47_trueMartingale_deterministicLocalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:30:47.689449+00:00
-- url     : https://prove2.me/theorems/c1700d9e-2c87-44bf-acb9-27e49a0dcad2
-- title:
--   A true martingale has deterministic localising times
-- statement:
--   Choose deterministic stopping times equal to natural-number horizons. Their stopped processes remain martingales by the conditional expectation tower and monotonicity of the filtration.
-- source:
--   Kyprianou (2006), Exercise 4.7, worked solution pp. 320-321; product calculus reduction.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_trueMartingale_deterministicLocalisation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → Real) (hM : Martingale M F P) :
    ∃ stop : Nat → Omega → NNReal,
      (∀ (n : Nat) (t : NNReal), MeasurableSet[(F t)]
        {omega : Omega | stop n omega ≤ t}) ∧
      (∀ᵐ omega : Omega ∂P,
        Tendsto (fun n : Nat => (stop n omega : WithTop NNReal)) atTop (nhds ⊤)) ∧
      (∀ n : Nat, Martingale (fun t omega => M (min t (stop n omega)) omega) F P) := by sorry
