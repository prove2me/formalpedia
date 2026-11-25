-- Prove2me | Theorems.Thm_Kyprianou_Ch04_markedExpectedIntegralExhaustion
-- name    : Kyprianou.Ch04.markedExpectedIntegralExhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:54:31.529864+00:00
-- url     : https://prove2.me/theorems/7dc7ba0a-8a56-425c-86b8-2870862f29cf
-- title:
--   Expected marked clock integral along increasing finite bands
-- statement:
--   The finite-band clock construction gives almost-everywhere measurable inner integrals. Directed continuity of the set integral and the monotone convergence theorem extend the expected integrals to the union of the bands.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem markedExpectedIntegralExhaustion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R : Omega → Measure (Real × Real))
    (hR : ∀ S : Set (Real × Real), MeasurableSet S →
      Measurable (fun w => R w S))
    (t : NNReal) (B : Nat → Set Real) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (hFin : ∀ n, ∀ᵐ w ∂P, R w (Set.Icc (0 : Real) (t : Real) ×ˢ B n) ≠ ⊤)
    (f : ((NNReal × Omega) × Real) → ENNReal) (hf : Measurable[F.predictable.prod inferInstance] f) :
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
        f ((z.1.toNNReal, w), z.2) ∂(R w) ∂P) =
    ⨆ n, (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ (B n),
        f ((z.1.toNNReal, w), z.2) ∂(R w) ∂P) := by
  sorry
end Kyprianou.Ch04
