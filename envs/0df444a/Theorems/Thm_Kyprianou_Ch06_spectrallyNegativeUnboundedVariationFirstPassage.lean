-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spectrallyNegativeUnboundedVariationFirstPassage
-- name    : Kyprianou.Ch06.spectrallyNegativeUnboundedVariationFirstPassage
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:12:26.612388+00:00
-- url     : https://prove2.me/theorems/57317eba-89f5-422f-b67b-afd33d9221aa
-- title:
--   Exercise 6.2: first-passage drift, upper slope and lower Wiener–Hopf decay
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, with ascending first-passage times τ⁺ and right-inverse Laplace exponent Φ: (i) show the deterministic drift of the possibly killed τ⁺ subordinator vanishes; (ii) show τ⁺_x/x→0 as x↓0, limsup_{t↓0}X_t/t=∞, origin regularity for (0,∞), and infinite ladder jump measure; (iii) show that E exp(θ inf_{s≤e_q}X_s)→0 as θ→∞ at independent Exp(q) time and recover open upper regularity. The printed infimum bar is verified visually in the PDF.
-- source:
--   Kyprianou (2006), Exercise 6.2(i)–(iii), printed p. 175; physical PDF p. 93.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.2: zero drift of the ascending first-passage subordinator
for a spectrally negative Levy process of unbounded variation; the
small-level first-passage limit, infinite upper small-time slope,
strict upper regularity, infinite ladder jump intensity; and the
Laplace-transform decay of the independent-exponential-time INFIMUM. -/
theorem spectrallyNegativeUnboundedVariationFirstPassage
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (nu : Measure Real)
    (psi : NNReal → Real) (Phi : NNReal → NNReal)
    (kill drift : NNReal) (ladderJump : Measure NNReal)
    (e : Omega → NNReal) (q : Real)
    (hX : IsRealLevyProcess P X)
    (hTriplet : IsLevyKhintchineTriplet P X b sigma2 nu)
    (hNoPositiveJumps : nu (Set.Ioi 0) = 0)
    (hUnboundedVariation : ¬ (sigma2 = 0 ∧
      (∫⁻ y in {y : Real | |y| < 1},
        ENNReal.ofReal |y| ∂nu) < ⊤))
    (hLaplace : ∀ (t lambda : NNReal),
      (∫ omega,
        Real.exp ((lambda : Real) * X t omega) ∂P) =
          Real.exp ((t : Real) * psi lambda))
    (hRightInverse : ∀ a : NNReal,
      psi (Phi a) = (a : Real))
    (hLadderMeasure : ladderJump {0} = 0 ∧
      (∫⁻ y : NNReal, ENNReal.ofReal (min 1 (y : Real))
        ∂ladderJump) < ⊤)
    (hLadderExponent : ∀ a : NNReal,
      (Phi a : Real) = (kill : Real) +
        (drift : Real) * (a : Real) +
        (∫⁻ y : NNReal,
          ENNReal.ofReal
            (1 - Real.exp (-(a : Real) * (y : Real)))
          ∂ladderJump).toReal)
    (hPassageTransform : ∀ (a x : NNReal),
      (∫ omega,
        if firstEntranceTime X 0 (Set.Ioi (x : Real)) omega = ⊤
        then (0 : Real)
        else Real.exp (-(a : Real) *
          (↑((firstEntranceTime X 0
             (Set.Ioi (x : Real)) omega).untopD 0) : Real)) ∂P) =
        Real.exp (-(x : Real) * (Phi a : Real)))
    (hq : 0 < q)
    (hExp : ∀ t : NNReal,
      P {omega | t < e omega} =
        ENNReal.ofReal (Real.exp (-q * (t : Real))))
    (hIndependent : ∀ (k : Nat) (times : Fin k → NNReal)
      (A : Fin k → Set Real) (B : Set NNReal),
      (∀ i, MeasurableSet (A i)) → MeasurableSet B →
      P {omega | e omega ∈ B ∧
        (∀ i : Fin k, X (times i) omega ∈ A i)} =
        P {omega | e omega ∈ B} *
        P {omega | ∀ i : Fin k, X (times i) omega ∈ A i}) :
    (drift = 0) ∧
    (∀ᵐ omega ∂P,
      Tendsto (fun x : NNReal =>
        (firstEntranceTime X 0 (Set.Ioi (x : Real))
          omega).untopD 0 / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ᵐ omega ∂P,
      ∀ M : Real, ∀ delta : NNReal, 0 < delta →
        ∃ t : NNReal, 0 < t ∧ t < delta ∧
          M < X t omega / (t : Real)) ∧
    IsRegularFor P X 0 (Set.Ioi 0) ∧
    ladderJump (Set.Ioi 0) = ⊤ ∧
    Tendsto (fun theta : Real =>
      ∫ omega,
        Real.exp (theta *
          sInf ((fun s : NNReal => X s omega) ''
            Set.Icc 0 (e omega))) ∂P)
      atTop (nhds 0) := by
  sorry

end Kyprianou.Ch06
