-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_original_completed_residual_source
-- name    : OAI.SevenEighths.InverseReflectedPhase.original_completed_residual_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:28:54.870414+00:00
-- url     : https://prove2.me/theorems/a4673227-ea50-4a14-9ee4-e0b52ab12803
-- title:
--   The completed residual source as frozen inactive physical terms
-- statement:
--   For parents, nonzero $J$, squarefree $F$, $m\ne0$, a unit $v$, $Q\ne0$, $c$ with $(c)=(9)Q(72)$, geometries $G_h$, residual rows coprime to $Q(72)$, slot lists of maximal ideals avoiding `goodLambda`, and the further data of the Lean ($W$, $X$, $w$, controlled strata $D$), OpenAI's completed residual source equals $\texttt{thetaDerivativeScalar}^{-1}\sum_h(\dots)\sum_A\texttt{frozenInactiveWeight}\,J\,F\,((m)F)\,(Q(72))\,A\sum_T\texttt{originalInactivePhysical}(\dots,D\,h\,A\,T,G_h.\mathrm{shape},\dots,W,X,w,K)$, as written in the Lean.
--
--   Lean: `OAI.SevenEighths.InverseReflectedPhase.original_completed_residual_source` in `lean/OAI/NumberTheory/DirichletL/Reflection/CompletedFiberSource.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (parents : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : Squarefree F)
    (m : Eis) (hm : m≠0) (hparents : ∀ I∈parents,I≠0) (v : Eisˣ)
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)

variable (Q : Ideal Eis) (hQ : Q≠0) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (hcop : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),IsCoprime (Q*Ideal.span {(72:Eis)}) K)
    (lists : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
    (hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
    (hodd : ∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2)
    (hperiod : ∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P)

variable (D : ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
    ∀ T : Finset σ,OriginalSplitCompletion (N:=(9:Eis)*c) (a:=(G h).a0) (c:=(G h).c0) (mode:=(G h).mode)
      ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
      (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
      (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
      lists hmax hgood T)

include hJ hQ hcQ hcop hdis hodd hperiod

theorem original_completed_residual_source
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W) (lo hi : ℝ) (hlo : 0<lo)
    (hsupp : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X)
    (w : ∀ i,lists i→ℂ) (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val))) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},
      fixedThetaRowCoeff c hc ((residualOriginalData parents J F hF m hm hparents v K).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
          frozenInactiveWeight J F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
            (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
            (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
            lists hmax hgood T (D h A T) (G h).shape (G h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val) W X w K := by
  sorry
end
end SevenEighths.InverseReflectedPhase

end OAI
end
