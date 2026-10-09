-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_actual_additive_gram_bound
-- name    : OAI.SevenEighths.ProbeGramCommon.actual_additive_gram_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:29:14.413706+00:00
-- url     : https://prove2.me/theorems/08c072b1-e623-4c72-873a-7515730700e6
-- title:
--   Additive Gram bound for low Gauss columns
-- statement:
--   For $0<\delta<1$, $0<a<b$, $M_0\ge0$ and a smooth compactly supported $W$ with support in $[a,b]$ and $|W|\le M_0$, there is $J$ such that for every finite set $S$ of maximal ideals containing `fixedBadPrimes` and Schwartz $U$ there is $K>0$ with: for every ray-ring element $\sigma$, reals $v$, $Y\ge1$, $Q>0$ with $Y^2/Q\ge1$,
--   $$\|\texttt{gaussEnergy}(\texttt{lowGaussColumns}\,W\,Y,\dots,\texttt{lowGaussColumn}(\texttt{calibrationForSet}\,S)\,W\,Y\,\sigma\,v,U,Q)\|\le K(1+|v|)^J\frac QY\Big(1+(Y^2/Q)^{1/6}+\frac{(Y^2/Q)^2}{Y}\Big)Y^{\delta}.$$
--
--   Lean: `OAI.SevenEighths.ProbeGramCommon.actual_additive_gram_bound` in `lean/OAI/NumberTheory/DirichletL/Detector/GramBound.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem actual_additive_gram_bound (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃J : ℕ,∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀U : SchwartzMap ℝ ℂ,
    ∃K : ℝ,0<K ∧ ∀(σ : RayRing)(v Y Q : ℝ)(hY : 1≤Y),0<Q→1≤Y^2/Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y (lt_of_lt_of_le zero_lt_one hY))
        (fun I=>primaryGenerator I.val) (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q‖≤
      K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ := by
  sorry

end SevenEighths.ProbeGramCommon
end

end OAI
end
