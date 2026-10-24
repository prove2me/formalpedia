-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_lower
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_local_order_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:45:04.670846+00:00
-- url     : https://prove2.me/theorems/8ddd0c72-d9b0-4708-a57e-5bc20302247c
-- title:
--   Jet vanishing gives a local order bound on the fibre
-- statement:
--   At every place, translated coefficient vanishing below the strict weighted jet threshold forces the derivative’s evaluation order to dominate the logarithmic ideal contact times the residual threshold. The equality case in the word-cost bound retains the threshold (1+2σ)N. The scale identity R=eᵢvᵢ converts the minimum weighted coordinate order into the displayed factor R.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_local_order_lower
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (N : Nat) (hN : 0 < N) (F : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 3 * (sigma : Real)) * (N : Real)) F)
    (word : List (Fin m))
    (hword : fibreContactWordCost (fun i => v i.succ) word ≤
      (sigma : Real) * (N : Real))
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) (fibreContactWord word F) ≠ 0) :
    ((polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) *
      ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu
          (MvPolynomial.aeval (fun i => x i.succ) (fibreContactWord word F)) : Real) := by sorry
