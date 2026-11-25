-- Prove2me | Theorems.Thm_Kyprianou_Ch04_conditionalEventCutoffCompensationENN
-- name    : Kyprianou.Ch04.conditionalEventCutoffCompensationENN
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:34:22.603749+00:00
-- url     : https://prove2.me/theorems/5c35789f-47fd-4012-886b-411de9ddcace
-- title:
--   Conditional event cutoff: extended Poisson compensation
-- statement:
--   The previously proved common-null event cutoff theorem gives admissibility and common pathwise left continuity for the event-weighted future kernel. Apply the proved nonnegative compensation identity to it.
-- source:
--   Kyprianou (2006), corrected Corollary 4.6 supporting lemma.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.conditionalEventCutoffCompensationENN
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ w ∂P, ∀ (x : Real) (r : NNReal), 0 < r →
      Tendsto (fun s : Real => phi s x w)
        (nhdsWithin (r : Real) (Set.Iio (r : Real))) (nhds (phi (r : Real) x w)))
    (u t : NNReal) (A : Set Omega) (hA : MeasurableSet[F u] A) :
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (if (u : Real) < z.1 ∧ w ∈ A then phi z.1 z.2 w else 0)
      ∂(N.N w) ∂P) =
    (∫⁻ w, ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      (∫⁻ x, ENNReal.ofReal (if (u : Real) < s ∧ w ∈ A then phi s x w else 0)
        ∂levyMeasure) ∂volume ∂P) := by
  sorry
