-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_5BivariateAscendingLadderJumpMeasure
-- name    : Kyprianou.Ch07.exercise7_5BivariateAscendingLadderJumpMeasure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T15:01:43.78337+00:00
-- url     : https://prove2.me/theorems/58321891-9f0c-4df6-b08d-8230391b1608
-- title:
--   Exercise 7.5: general and spectrally positive ascending ladder jump laws
-- statement:
--   Exercise 7.5, both requested measure identities on measurable time-height rectangles. For the actual non-compound-Poisson Lévy process X with original Lévy measure Π, the bivariate ascending ladder process has Lévy jump measure ΠAsc determined by its small-time increment law. The descending bivariate ladder potential Uhat is determined from the original inverse local time and running maximum of −X. First prove ΠAsc(dt,dh)=∫_[0,∞) Uhat(dt,dθ) Π(dh+θ). If X is spectrally positive, additionally prove ΠAsc(dt,dh)=∫₀∞ dθ P(inverse local time at the descending maximum at θ∈dt) Π(dh+θ). The ascending/descending local-time scales obey the Chapter 6 Wiener-Hopf product normalisation at q=1 (printed p.159); the spectrally positive formula uses descending ladder height normalised to unit drift on positive surviving epochs (p.208).  PiAsc is identified through the small-time expected count of actual nonzero jumps of the time-height ladder path, using inverse local-time left limits; ladder drift contributes no jumps. The printed Exercise 7.5 invokes Exercise 5.4; the descending potential and both jump-measure identities remain unchanged. Chapter 7 opening (printed p. 179, PDF p. 188) explicitly excludes subordinators throughout the chapter. This hypothesis is necessary in the spectrally positive specialisation: a strictly increasing Lévy path has descending ladder height zero, and the textbook normalisation of descending ladder height to unit slope is then inapplicable. Both original Exercise 7.5 identities remain intact.
-- source:
--   Kyprianou (2006), Exercise 7.5, both formulae printed p.208; original PDF page 217, Windows Ky.pdf sheet 109.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Exercise 7.5: the bivariate ascending ladder jump measure identity,
followed by the spectrally positive time-height specialisation. -/
theorem exercise7_5BivariateAscendingLadderJumpMeasure
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup Ldown : NNReal → Omega → NNReal)
    (b : Real) (sigma2 : NNReal)
    (Pi : Measure Real)
    (PiAsc Uhat : Measure (NNReal × Real))
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hNotSubordinator : ¬ Kyprianou.Ch06.IsSubordinatorProcess P X)
    (hXTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hUp : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum P F X Lup)
    (hDown : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
      P F (fun t omega => -X t omega) Ldown)
    (hWienerHopfScale :
      Real.log
        (∫ omega,
          let tau := Kyprianou.Ch06.inverseLocalTime Lup 1 omega
          if tau = ⊤ then (0 : Real)
          else Real.exp (-((tau.untopD (0 : NNReal) : NNReal) : Real)) ∂P) *
      Real.log
        (∫ omega,
          let tau := Kyprianou.Ch06.inverseLocalTime Ldown 1 omega
          if tau = ⊤ then (0 : Real)
          else Real.exp (-((tau.untopD (0 : NNReal) : NNReal) : Real)) ∂P) = 1)
    (hSpectralPositiveUnitDescendingHeight :
      Pi (Set.Iio 0) = 0 →
      ∀ᵐ omega ∂P, ∀ s : NNReal,
        let tau := Kyprianou.Ch06.inverseLocalTime Ldown s omega
        tau ≠ ⊤ → 0 < tau.untopD 0 →
          Kyprianou.Ch06.runningMaximum
            (fun t w => -X t w) (tau.untopD 0) omega = (s : Real))
    (hAscJumpMeasure : ∀ B : Set (NNReal × Real),
      MeasurableSet B → (0 : NNReal × Real) ∉ B →
      Tendsto (fun h : Real =>
        ENNReal.ofReal (1 / h) *
          (∫⁻ omega,
            (∑' s : NNReal,
              if 0 < s ∧ s ≤ Real.toNNReal h then
                let tau := Kyprianou.Ch06.inverseLocalTime Lup s omega
                let tauLeft :=
                  Kyprianou.Ch06.inverseLocalTimeLeft Lup s omega
                if tau ≠ ⊤ ∧ tauLeft ≠ ⊤ ∧
                    ((tau.untopD 0 - tauLeft.untopD 0),
                     Kyprianou.Ch06.runningMaximum X (tau.untopD 0) omega -
                     Kyprianou.Ch06.runningMaximum X (tauLeft.untopD 0) omega)
                      ∈ B
                then (1 : ENNReal) else 0
              else 0) ∂P))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (PiAsc B)))
    (hUhat : ∀ B : Set (NNReal × Real), MeasurableSet B →
      Uhat B =
        ∫⁻ s : Real in Set.Ici 0,
          P {omega | let tau :=
            Kyprianou.Ch06.inverseLocalTime Ldown (Real.toNNReal s) omega
            tau ≠ ⊤ ∧
            ((tau.untopD 0),
             Kyprianou.Ch06.runningMaximum
                (fun t omega => -X t omega) (tau.untopD 0) omega) ∈ B}
          ∂volume) :
    ((∀ (At : Set NNReal) (Ah : Set Real),
      MeasurableSet At → MeasurableSet Ah →
      (∀ h : Real, h ∈ Ah → 0 < h) →
      PiAsc {zh | zh.1 ∈ At ∧ zh.2 ∈ Ah} =
        ∫⁻ zt : NNReal × Real in {zt | zt.1 ∈ At ∧ 0 ≤ zt.2},
          Pi {z : Real | z - zt.2 ∈ Ah} ∂Uhat) ∧
     (Pi (Set.Iio 0) = 0 →
       ∀ (At : Set NNReal) (Ah : Set Real),
       MeasurableSet At → MeasurableSet Ah →
       (∀ h : Real, h ∈ Ah → 0 < h) →
       PiAsc {zh | zh.1 ∈ At ∧ zh.2 ∈ Ah} =
         ∫⁻ theta : Real in Set.Ici 0,
           P {omega | let tau :=
             (Kyprianou.Ch06.inverseLocalTime Ldown
               (Real.toNNReal theta) omega)
             tau ≠ ⊤ ∧ (tau.untopD 0) ∈ At} *
           Pi {z : Real | z - theta ∈ Ah} ∂volume)) := by
  sorry

end Kyprianou.Ch07
