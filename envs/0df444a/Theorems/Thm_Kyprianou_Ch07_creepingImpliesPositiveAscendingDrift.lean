-- Prove2me | Theorems.Thm_Kyprianou_Ch07_creepingImpliesPositiveAscendingDrift
-- name    : Kyprianou.Ch07.creepingImpliesPositiveAscendingDrift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:57:48.177933+00:00
-- url     : https://prove2.me/theorems/46620cdf-c4ec-45b7-9101-a02aba0645d7
-- title:
--   Lemma 7.10, forward direction: upward creeping implies positive ascending ladder-height drift
-- statement:
--   Use the ascending ladder-height subordinator renewal measure and the positive creeping mass to establish a nonzero drift coefficient, identified with the large-beta ladder exponent slope.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.10 and proof, printed p. 194; original PDF p. 203. Exact two implications of published Chapter 7 Lemma 7.10, target c7514e68-6416-4bcc-890a-9ee6f7764de9; source retains the actual ladder exponent and non-compound-Poisson/local-time hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.creepingImpliesPositiveAscendingDrift
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (L : NNReal → Omega → NNReal)
    (kappa : Complex → Complex → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hL : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum P F X L)
    (hKappa : ∀ (a b : Complex),
      0 ≤ a.re → 0 ≤ b.re → ∀ t : NNReal,
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime L t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp
          (-a * (↑((tau.untopD 0 : NNReal) : Real) : Complex) -
            b * (↑(Kyprianou.Ch06.runningMaximum X
                (tau.untopD 0) omega) : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) * kappa a b)) :
    ∀ x : Real, 0 < x →
      0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) x →
        ∃ d : Real, 0 < d ∧
          Tendsto (fun beta : Real =>
            (kappa 0 (beta : Complex)).re / beta)
            atTop (nhds d) := by
  sorry
