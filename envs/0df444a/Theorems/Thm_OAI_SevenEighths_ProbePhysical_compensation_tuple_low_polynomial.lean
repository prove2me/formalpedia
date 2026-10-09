-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_compensation_tuple_low_polynomial
-- name    : OAI.SevenEighths.ProbePhysical.compensation_tuple_low_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:19.471385+00:00
-- url     : https://prove2.me/theorems/3ec3eb8c-e0db-49bd-ac47-34a68c7693cd
-- title:
--   Compensation tuples rewritten through low separated integrals
-- statement:
--   For $\eta$, $S$ maximal containing `fixedBadPrimes`, $W_0$ smooth and $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$), slot sets of nonzero elements, $J$, slot weights $W$, sizes $P$, and reals $X,Y,T>0$, $t$: the sum over slot tuples of `compensationSubsetWeight`·`compensationRowTest`·`selectedSlotFactor` equals the sum over `LowUnselectedTuple`s $a$ of `lowUnselectedWeight` times $\big(\sqrt{\texttt{lowPhysicalScale}(X/\nu_a,Y/\nu_a)}\big)^{-1}(2\pi)^{-1}\int$`lowSeparatedIntegrand`$(\dots,X/\nu_a,Y/\nu_a,\texttt{lowSelectedInverseRow}\dots)(v)\,dv$, where $\nu_a$ is the `elementNorm` of the product of the unselected entries.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.compensation_tuple_low_polynomial` in `lean/OAI/NumberTheory/DirichletL/Detector/LowSlotPolynomial.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem compensation_tuple_low_polynomial {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    (∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
      compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
        selectedSlotFactor W P (fun i=>(p i).val) J t)=
      ∑a : LowUnselectedTuple slots J,lowUnselectedWeight slots J W P a*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
          ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
            (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
            (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
            (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
              η S hS (lowSelectedIdeal slots J) T t) v := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
