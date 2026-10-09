-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_original_selected_reflected_expansion
-- name    : OAI.SevenEighths.InverseReflectedPhase.original_selected_reflected_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:25:39.242986+00:00
-- url     : https://prove2.me/theorems/770eb849-5ad1-4bec-ae0f-39b3fa401f6b
-- title:
--   Reflected expansion of the selected original row
-- statement:
--   For good mask row data $D$ (for $m,f,z$), ideals $R\ne0$, $I\ne0$, squarefree $F$, $Q_0$, a prime family $S$, and the further data of the Lean (geometries $G_h$, controlled strata $C(h,B,T)$, $W$, $X$), OpenAI's selected original row equals a finite sum over $h\in\mathcal O/(c)$, subsets $B$ of the pool and $T$ of the slots, of explicit coefficients (products of $1-N(b)^{-1}$ over pool primes of local exponent $0$ and of $N(S_t)^{-1}$ over unselected slots) times `mixedReflectedValue (C h B T) (G h).shape … (reflectedExponent …) (slotIndices B (PrimeIndex K) T) W X`, as written in the Lean.
--
--   Lean: `OAI.SevenEighths.InverseReflectedPhase.original_selected_reflected_expansion` in `lean/OAI/NumberTheory/DirichletL/Reflection/SelectedExpansion.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B026

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "Pall" => PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S
local notation "Jall" => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
  Multiset.count (Subtype.val (Subtype.val P)) (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal)%6) (fun _ : σ => 0)

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem original_selected_reflected_expansion
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hSodd : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal Q₀, ∀ i, S.ideal i≠P.val.val)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1) (hQ₀ : Q₀≠0)
    (hφperiod : CanonicalCoefficientClass.FactorsModulo Q₀ φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q₀)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((Pall).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist (Pall).generator (Pall).generator_good Jall markedSumSlots) W X
      (fun A => ∏ i∈markedSumSlots, if Ideal.span {(Pall).generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
        ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
          if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
          ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
        mixedReflectedValue (C h B T) (G h).shape
          (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_ne_zero
          (G h).denominator_ne_zero
          (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_good
          (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
          (slotIndices B (PrimeIndex K) T) W X := by
  sorry
end
end SevenEighths.InverseReflectedPhase

end OAI
end
