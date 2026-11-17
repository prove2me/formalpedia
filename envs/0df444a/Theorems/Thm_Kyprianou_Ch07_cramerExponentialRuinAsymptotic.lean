-- Prove2me | Theorems.Thm_Kyprianou_Ch07_cramerExponentialRuinAsymptotic
-- name    : Kyprianou.Ch07.cramerExponentialRuinAsymptotic
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:59:29.448291+00:00
-- url     : https://prove2.me/theorems/ec206d21-3083-4fd0-a1ed-658452e9e426
-- title:
--   Theorem 7.6: Cramér’s precise exponential ruin estimate
-- statement:
--   For a real Lévy process X with nonmonotone paths drifting to minus infinity, suppose the Cramér condition ψ(ν)=0 holds for ν>0 with ψ(θ)=log E exp(θX₁) and the Lévy jump measure has nonlattice support when its total mass is finite. Let κ(0,β) be the actual ascending ladder Laplace exponent, tied to the admissible local time. Then lim_{x→∞} e^{νx}P(τ⁺_x<∞)=κ(0,0)/(ν κ'_{β}(0,−ν)). The extended nonnegative right derivative may be infinite; in that case the limit is zero. The statement preserves all three source conditions and the infinite-derivative boundary case. The positivity of the ascending ladder killing rate and existence and strictly positive value (possibly infinite) of the right derivative at minus nu are conclusions, derived alongside the Cramer asymptotic, rather than hypotheses.
-- source:
--   Kyprianou (2006), Theorem 7.6(i)–(iii) and equation (7.6), printed pp.185–186, original PDF physical pp.194–195, Windows Ky.pdf sheets 98.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.6: the Cramér ruin constant, including the zero
limit when the right derivative of the ascending ladder exponent
at -ν is infinite. -/
theorem cramerExponentialRuinAsymptotic
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup : NNReal → Omega → NNReal)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (psi kappa : Real → Real)
    (nu : Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet
      P X b sigma2 Pi)
    (hNoMonotonePaths :
      (¬ ∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega)) ∧
      (¬ ∀ᵐ omega ∂P, Monotone (fun t : NNReal => -X t omega)))
    (hDriftsDown : ∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atBot)
    (hNu : 0 < nu)
    (hMGF : ∀ theta : Real, 0 ≤ theta → theta ≤ nu →
      (∫ omega, Real.exp (theta * X 1 omega) ∂P) =
        Real.exp (psi theta))
    (hCramer : psi nu = 0)
    (hNonLattice : Pi Set.univ < ⊤ →
      ∀ delta : Real, 0 < delta →
        0 < Pi {x : Real | ∀ k : Int, x ≠ delta * (k : Real)})
    (hLocalTime : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
      P F X Lup)
    (hAscLaplace : ∀ theta : Real, -nu ≤ theta →
      ∀ t : NNReal,
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Lup t omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-theta *
          Kyprianou.Ch06.runningMaximum X (tau.untopD 0) omega) ∂P) =
        Real.exp (-(t : Real) * kappa theta))
    :
    ∃ derivativeAtMinusNu : ENNReal,
      0 < kappa 0 ∧
      0 < derivativeAtMinusNu ∧
      Tendsto
        (fun h : Real => ENNReal.ofReal
          ((kappa (-nu + h) - kappa (-nu)) / h))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds derivativeAtMinusNu) ∧
      Tendsto (fun x : Real =>
        Real.exp (nu * x) *
          (P {omega | Kyprianou.Ch05.PassageFinite
            X (fun _ => (⊤ : WithTop NNReal)) x omega}).toReal)
        atTop
        (nhds ((ENNReal.ofReal (kappa 0) /
          (ENNReal.ofReal nu * derivativeAtMinusNu)).toReal)) := by
  sorry

end Kyprianou.Ch07
