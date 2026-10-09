-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_continued_source_slices
-- name    : OAI.SevenEighths.ProbePrincipalContours.continued_source_slices
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:47.175567+00:00
-- url     : https://prove2.me/theorems/3a5539be-4908-42f1-bf1e-048445712ea7
-- title:
--   Slice integrals of the continued source integrand decay
-- statement:
--   With $\eta,S,J,T,b,W_0,W_1,a_0,b_0,a_1,b_1$ as in the joint-integrability statement, reals $X,Y,Z>0$, $a\ge7/8$ with `beta` $<a$, $\xi\ge33/200$ with $6\xi\ne1$, $c_w>1$, $\upsilon\in[19/20,c_w]$ with $\upsilon\ne1$, and $N\in\mathbb N$: there are $C\ge0$, $K>0$ such that for every `SliceAxis` and every $R$, with $F$ the continued source integrand on `HeightSpace` (the multiplier at $(a+ip_{11},\upsilon+ip_2,\xi+ip_{12})$ times the two principal L-functions), the slice $q\mapsto F(\texttt{sliceMap axis R q})$ is integrable on $\mathbb R^2$ and its $L^1$ norm is at most `arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6ξ-1|`$\cdot K/\texttt{height}(R)^N$.
--
--   Lean: `OAI.SevenEighths.ProbePrincipalContours.continued_source_slices` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

local instance instCountableO_r7ce669_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_r7ce669_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
theorem continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) (N : ℕ) :
    ∃ C K : ℝ, 0≤C ∧ 0<K ∧ ∀axis : SliceAxis,∀R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume)≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1| *K/height R^N := by
  sorry

end SevenEighths.ProbePrincipalContours
end

end OAI
end
