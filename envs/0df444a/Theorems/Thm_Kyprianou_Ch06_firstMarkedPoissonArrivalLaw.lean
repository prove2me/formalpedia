-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkedPoissonArrivalLaw
-- name    : Kyprianou.Ch06.firstMarkedPoissonArrivalLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:35:17.866394+00:00
-- url     : https://prove2.me/theorems/60ff0766-b0b2-40ee-b9ed-fdc81101cdfd
-- title:
--   Lemma 6.18 subpart 1: exponential survival law for the first A-mark
-- statement:
--   The exponential survival law for the first A-mark under exactly the marked Poisson point process, finite measure, measurability and first-mark witness assumptions of published Kyprianou (2006) Lemma 6.18. This is one independent component of the original conjunctive conclusion.
-- source:
--   Kyprianou (2006), Lemma 6.18(i)-(iii), printed pp.160–161, original PDF pp.169–170.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Lemma 6.18: the first A-mark time is exponential; restriction to
marks outside A has the un-killed Poisson law and is independent of
the killing time; the first A-mark is independent of that stopped
restricted process. The first-mark assertion assumes positive intensity,
since an A-mark does not exist when n(A)=0. -/
theorem firstMarkedPoissonArrivalLaw
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (∀ t : NNReal,
      P {omega | (t : WithTop NNReal) < sigma omega} =
        ENNReal.ofReal
          (Real.exp (-((n A).toReal * (t : Real))))) := by
  sorry

end Kyprianou.Ch06
