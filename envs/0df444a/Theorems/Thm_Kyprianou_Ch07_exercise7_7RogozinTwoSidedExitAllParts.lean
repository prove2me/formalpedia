-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_7RogozinTwoSidedExitAllParts
-- name    : Kyprianou.Ch07.exercise7_7RogozinTwoSidedExitAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T15:03:52.308682+00:00
-- url     : https://prove2.me/theorems/da1475bf-a46d-4949-bfe6-5990f2afa670
-- title:
--   Exercise 7.7: stable two-sided exit CDFs, coupled system and Rogozin solution
-- statement:
--   Exercise 7.7 in all three source parts. For a two-sided-jump nonmonotone α-stable Lévy process with α∈(0,2), symmetry parameter β∈(−1,1), positivity parameter ρ∈(0,1), and the stable-process Zolotarev relation ρ=1/2+arctan(β tan(πα/2))/(πα) for α≠1 (β=0 at α=1), and α ρ,α(1−ρ)∈(0,1): (i) derive Rogozin's two explicit one-sided overshoot CDFs for first strict exit above one and below zero, with Φ_q(y)=sin(πq)/π ∫₀ʸt^(−q)/(1+t)dt. (ii) For starting x∈(0,1), let r(x,dy) and l(x,dy) be the actual upper-first and lower-first overshoot subprobability measures. Prove both coupled integral equations against the opposite measure. (iii) Assuming uniqueness of solutions to these coupled equations, derive the source analytic formula r(x,y)=(sin(παρ)/π)(1−x)^(αρ)x^(α(1−ρ))∫₀ʸt^(−αρ)(1+t)^(−α(1−ρ))/(t+1−x)dt, and the symmetric expression for l(x,y), with denominator t+x. Every random variable is defined by the original Lévy path and genuine first exit clocks. At the starting boundary x=1 for the upper barrier and x=0 for the lower barrier, the one-sided CDF is defined as the corresponding limiting value one for y≥0, rather than taking a zero-denominator quotient.
-- source:
--   Kyprianou (2006), Exercise 7.7(i)–(iii), printed p.209, original PDF p.218, Windows Ky.pdf sheet 110.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch07_StableTwoSidedExitObservables
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Exercise 7.7(i)-(iii): both one-sided exit CDFs, the coupled
two-sided exit equations, and the Rogozin explicit solutions. -/
theorem exercise7_7RogozinTwoSidedExitAllParts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (alpha rho beta : Real)
    (Pi : Measure Real) (b : Real) (sigma2 : NNReal)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hAlpha : 0 < alpha ∧ alpha < 2)
    (hBeta : -1 < beta ∧ beta < 1)
    (hBetaZeroAtOne : alpha = 1 → beta = 0)
    (hStableSymmetry :
      alpha ≠ 1 →
        rho = 1 / 2 +
          Real.arctan (beta * Real.tan (Real.pi * alpha / 2)) /
            (Real.pi * alpha))
    (hRho : 0 < rho ∧ rho < 1)
    (hStableRange : 0 < alpha * rho ∧ alpha * rho < 1 ∧
      0 < alpha * (1 - rho) ∧ alpha * (1 - rho) < 1)
    (hStableScaling : ∀ t : NNReal, 0 < t →
      ∀ B : Set Real, MeasurableSet B →
      P {omega | X t omega ∈ B} =
        P {omega | ((t : Real) ^ (1 / alpha)) * X 1 omega ∈ B})
    (hPositivity : ∀ t : NNReal, 0 < t →
      P {omega | 0 ≤ X t omega} = ENNReal.ofReal rho)
    (hBothJumps : 0 < Pi (Set.Ioi 0) ∧ 0 < Pi (Set.Iio 0))
    (hExitLawMeasurability : ∀ x : Real,
      Measurable (fun omega =>
        x + X ((firstUpOfOne X x omega).untopD 0) omega - 1) ∧
      Measurable (fun omega =>
        -(x + X ((firstDownOfZero X x omega).untopD 0) omega))) :
    let r : Real → Measure Real := upperExitOvershootLaw P X
    let l : Real → Measure Real := lowerExitOvershootLaw P X
    let eqSystem : (Real → Measure Real) →
      (Real → Measure Real) → Prop := fun R L =>
      ∀ x y : Real, 0 < x → x < 1 → 0 ≤ y →
        ((R x (Set.Iic y)).toReal =
          rogozinPhi (alpha * rho) (y / (1 - x)) -
            ∫ z : Real in Set.Ioi 0,
              rogozinPhi (alpha * rho) (y / (1 + z)) ∂(L x)) ∧
        ((L x (Set.Iic y)).toReal =
          rogozinPhi (alpha * (1 - rho)) (y / x) -
            ∫ z : Real in Set.Ioi 0,
              rogozinPhi (alpha * (1 - rho)) (y / (1 + z)) ∂(R x))
    ((∀ x y : Real, x ≤ 1 → 0 ≤ y →
       P {omega | let tau := firstUpOfOne X x omega
         tau ≠ ⊤ ∧
         x + X (tau.untopD 0) omega ≤ 1 + y} =
         (if x = 1 then (1 : ENNReal) else
           ENNReal.ofReal (rogozinPhi (alpha * rho) (y / (1 - x))))) ∧
     (∀ x y : Real, 0 ≤ x → 0 ≤ y →
       P {omega | let tau := firstDownOfZero X x omega
         tau ≠ ⊤ ∧
         -(x + X (tau.untopD 0) omega) ≤ y} =
         (if x = 0 then (1 : ENNReal) else
           ENNReal.ofReal (rogozinPhi (alpha * (1 - rho)) (y / x)))) ∧
     eqSystem r l ∧
     ((∀ R L R2 L2 : Real → Measure Real,
        eqSystem R L → eqSystem R2 L2 →
          ∀ x : Real, 0 < x → x < 1 →
            (∀ B : Set Real, MeasurableSet B →
              R x B = R2 x B ∧ L x B = L2 x B)) →
       ∀ x y : Real, 0 < x → x < 1 → 0 ≤ y →
         (r x (Set.Iic y)).toReal =
           (Real.sin (Real.pi * alpha * rho) / Real.pi) *
           (1 - x) ^ (alpha * rho) * x ^ (alpha * (1 - rho)) *
           (∫ t : Real in Set.Ioc 0 y,
             t ^ (-alpha * rho) *
               (t + 1) ^ (-alpha * (1 - rho)) /
               (t + 1 - x) ∂volume) ∧
         (l x (Set.Iic y)).toReal =
           (Real.sin (Real.pi * alpha * (1 - rho)) / Real.pi) *
           x ^ (alpha * (1 - rho)) * (1 - x) ^ (alpha * rho) *
           (∫ t : Real in Set.Ioc 0 y,
             t ^ (-alpha * (1 - rho)) *
               (t + 1) ^ (-alpha * rho) /
               (t + x) ∂volume))) := by
  sorry

end Kyprianou.Ch07
