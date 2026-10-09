-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_low_central_gaussian_dyad
-- name    : OAI.SevenEighths.ProbePhysical.low_central_gaussian_dyad
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:49.541301+00:00
-- url     : https://prove2.me/theorems/57109767-0223-4226-8493-55b501c67c80
-- title:
--   Bound for the low common Gaussian dyad
-- statement:
--   Let $\eta$ be a `HeckeFamily.Character`, $S$ a finite set of maximal ideals containing `fixedBadPrimes`, $\ell_i\ge0$ ($i<K$) with $\sum\ell_i\le1/6$, reals $a>0$, $b$, $0<\varepsilon<1$, smooth $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$, $a_1<b_1$) with $|W_1|\le M$. Then there are a degree and $C>0$ such that for all sufficiently large $Z$ ($Z>1$): for all pairwise disjoint finite sets $T_i$ of `Supported` prime ideals outside $S$ with norms in $[aZ^{\ell_i},bZ^{\ell_i}]$, every $J$, every $U$ with $Z^{1+\lambda-\varepsilon/2}\le U\le Z^{1+\lambda+\varepsilon/2}$ ($\lambda=$`lowSelectedLength ℓ J`), slot weights bounded by 1 and compactly supported Schwartz $V$:
--   $$\|\texttt{lowCommonDyad}(\dots,Z^{17/48},Z^{23/48},U,Z^{1+\lambda},V)\|\le C\,Z^{3/16+254\varepsilon}\,\texttt{gaussianJointMoment}\,V\,\mathrm{degree}\,(U/Z^{1+\lambda}).$$
--
--   Lean: `OAI.SevenEighths.ProbePhysical.low_central_gaussian_dyad` in `lean/OAI/NumberTheory/DirichletL/Detector/LowGaussianDyad.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Definitions.Def_OAIHecke78B023

section

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0<U→
      Z^(1+lowSelectedLength ell J-ε/2)≤U→U≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
        W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) U
          (Z^(1+lowSelectedLength ell J)) V hV‖≤
        C*Z^(3/16+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
