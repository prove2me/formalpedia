-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_PrimeFamily_marked_reflected_source_of_controlled
-- name    : OAI.SevenEighths.InverseReflectedPhase.PrimeFamily.marked_reflected_source_of_controlled
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:15:09.016486+00:00
-- url     : https://prove2.me/theorems/08f9361c-51fd-41f1-bdff-4621725b2ba8
-- title:
--   The marked completed T-sum through controlled reflected values
-- statement:
--   Let $P$ be a finite `PrimeFamily` with pairwise coprime ideals of odd residue characteristic, $j_i<6$, $S$ finite, $\varphi$ multiplicative bounded by 1 factoring modulo $Q\ne0$, $c\ne0$ with $(c)\subseteq(9)Q$, geometries $G_h$ (`FixedFourierGeometry c h`) with $9\,c_0(G_h)\mid N$, controlled strata $C(h,A)$ for every $A$, $W$ smooth, compactly supported in $[lo,hi]$ ($lo>0$), $X>0$. Then `markedCompletedT (φ · unmarkedSexticTwist …) W X (A ↦ ∏_{i∈S}[p_i∣A])` equals
--   $$\texttt{thetaDerivativeScalar}^{-1}\sum_{h\in\mathcal O/(c)}\texttt{fixedThetaRowCoeff}\,c\,\varphi\,h\sum_{A}\texttt{localInactiveWeight}(\dots,A)\cdot\texttt{mixedReflectedValue}(C(h,A),G_h.\mathrm{shape},\dots,\texttt{activeMarks}\,A\,S,W,X).$$
--
--   Lean: `OAI.SevenEighths.InverseReflectedPhase.PrimeFamily.marked_reflected_source_of_controlled` in `lean/OAI/NumberTheory/DirichletL/Reflection/MarkedChosenDual.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B024

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

theorem marked_reflected_source_of_controlled
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedReflectedValue (C h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  sorry
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
end
