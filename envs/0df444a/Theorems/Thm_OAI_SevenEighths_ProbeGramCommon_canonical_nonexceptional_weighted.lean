-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_canonical_nonexceptional_weighted
-- name    : OAI.SevenEighths.ProbeGramCommon.canonical_nonexceptional_weighted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:47.384761+00:00
-- url     : https://prove2.me/theorems/56f4b4a5-88d4-4003-a3d2-b1310b8855de
-- title:
--   Decay of canonical lattice blocks at nonexceptional frequencies
-- statement:
--   For $A>2$ and $0<a_0<b_0$ there are $J$ and a finite $H_0$ such that for every smooth $W$ with support in $[a_0,b_0]$ there is $K>0$ with: for every finite set $S$ of maximal ideals, $\sigma$, supported ideal $C$, frequency $k$ that is not exceptional, $d$, Schwartz $U$ and reals $v$, $H,N>0$:
--   $$\|\texttt{canonicalLatticeBlock}\,S\,\sigma\,C\,k\,d\,W\,U\,v\,(N((k))/H)\,N\|\le K\|U\|_{H_0}(1+|v|)^JN(C)N^2\min\Big(1,\Big(\frac{N(\texttt{jointFixedModulus}\,S)N(C)H}{N}\Big)^A\Big)\Big(1+\frac{N((k))}H\Big)^{-2}.$$
--
--   Lean: `OAI.SevenEighths.ProbeGramCommon.canonical_nonexceptional_weighted` in `lean/OAI/NumberTheory/DirichletL/Detector/GramWeightedFrequency.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem canonical_nonexceptional_weighted (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)*
          (1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
  sorry

end SevenEighths.ProbeGramCommon
end

end OAI
end
