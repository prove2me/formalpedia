-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkedPoissonOutsideIndependence
-- name    : Kyprianou.Ch06.firstMarkedPoissonOutsideIndependence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:35:19.138718+00:00
-- url     : https://prove2.me/theorems/61bd98c5-96c0-4241-9bed-efdf22507da3
-- title:
--   Lemma 6.18 subpart 2: independence of outside-A Poisson counts before first A-mark
-- statement:
--   The independence of outside-A Poisson counts before first A-mark under exactly the marked Poisson point process, finite measure, measurability and first-mark witness assumptions of published Kyprianou (2006) Lemma 6.18. This is one independent component of the original conjunctive conclusion.
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
theorem firstMarkedPoissonOutsideIndependence
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
    (∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat) (t : NNReal),
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by
  sorry

end Kyprianou.Ch06
