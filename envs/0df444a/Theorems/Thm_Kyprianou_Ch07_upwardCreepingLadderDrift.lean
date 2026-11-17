-- Prove2me | Theorems.Thm_Kyprianou_Ch07_upwardCreepingLadderDrift
-- name    : Kyprianou.Ch07.upwardCreepingLadderDrift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:51:51.951508+00:00
-- url     : https://prove2.me/theorems/c7514e68-6416-4bcc-890a-9ee6f7764de9
-- title:
--   Lemma 7.10: upward creeping iff ascending ladder height has positive drift
-- statement:
--   For any real Lévy process X other than compound Poisson, choose an admissible local time L at its maximum and the genuine ascending bivariate ladder exponent κ tied to X,L via its complete inverse-local-time/height Laplace law. The process creeps upward at some and then every positive level x precisely when the spatial ladder-height exponent has strictly positive linear growth lim_{β→∞} κ(0,β)/β>0. The un-killed original process has first strict upcrossing time with infinite lifetime.
-- source:
--   Kyprianou (2006), Lemma 7.10, printed p.197, Windows Ky.pdf two-page sheet 104 (original p.206).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Lemma 7.10: for a non-compound-Poisson Lévy process,
upward creeping at one and hence every positive level is equivalent
to positive spatial drift of its actual ascending ladder height. -/
theorem upwardCreepingLadderDrift
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
      ((0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) x) ↔
        ∃ d : Real, 0 < d ∧
          Tendsto (fun beta : Real =>
            (kappa 0 (beta : Complex)).re / beta)
            atTop (nhds d)) := by
  sorry

end Kyprianou.Ch07
