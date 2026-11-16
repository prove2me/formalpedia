-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalJointOvershootUndershoot
-- name    : Kyprianou.Ch05.renewalJointOvershootUndershoot
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:49:53.042206+00:00
-- url     : https://prove2.me/theorems/c6c3ed98-0c9c-447f-b31c-d26e55829b55
-- title:
--   Lemma 5.5: renewal joint over/undershoot law and finite-mean limiting tail
-- statement:
--   Both original parts: the exact joint law V(x-dy) F(y+du) for u>0 and y in (0,x], and the nonlattice finite-positive-mean limit of P(overshoot>u, undershoot>y) as x->infinity, equal to the integrated F-tail from u+y to infinity divided by mean mu. The required nonexplosion of renewal epochs is made explicit and must be proved from the nondegenerate independent spacings; neither conclusion is presumed.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Lemma 5.5, pp.116-117: full finite-level joint law and
the nonlattice finite-mean limiting tail on two strict positive axes. -/
theorem renewalJointOvershootUndershoot
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
 :
  ((∀ (x : Real), 0 < x →
      ∀ (A B : Set Real), MeasurableSet A → MeasurableSet B →
        A ⊆ Set.Ioi (0 : Real) →
        B ⊆ Set.Ioc (0 : Real) x →
          P {omega : Omega |
            0 < renewalOvershoot Z x omega ∧
            renewalOvershoot Z x omega ∈ A ∧
            renewalUndershoot Z x omega ∈ B} =
          renewalJointKernel (renewalMeasure F) F x A B) ∧
   ((Integrable (fun z : Real => z) F) →

      NonLatticeMeasure F →
        ∀ (u y : Real), 0 < u → 0 < y →
          Tendsto
            (fun x : Real =>
              (P {omega : Omega |
                u < renewalOvershoot Z x omega ∧
                y < renewalUndershoot Z x omega}).toReal)
            atTop
            (nhds
              ((∫ z in Set.Ioi (u+y),
                 (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : Real, z ∂F)))))
 := by
  sorry

end Kyprianou.Ch05
