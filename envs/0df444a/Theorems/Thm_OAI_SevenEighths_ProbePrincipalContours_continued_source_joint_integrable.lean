-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_continued_source_joint_integrable
-- name    : OAI.SevenEighths.ProbePrincipalContours.continued_source_joint_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:44:03.669995+00:00
-- url     : https://prove2.me/theorems/e32a6915-f977-42cb-8b40-d37d3b99d3e4
-- title:
--   Joint integrability of the continued source integrand
-- statement:
--   With $\eta,S,J,T,b,W_0,W_1,a_0,b_0,a_1,b_1$ as in the residue-pair statement and reals $X,Y,Z>0$, $a\ge7/8$ with `beta` $<a$, $\xi\ge33/200$ with $6\xi\ne1$, $c_w>1$ and $\upsilon\in[19/20,c_w]$ with $\upsilon\ne1$: the function on `HeightSpace` sending $p$ to `continuedSourceMultiplier … (a+i p.1.1) (υ+i p.2) (ξ+i p.1.2)` times `LFunction (fixedSourcePrincipal S _) (6(ξ+i p.1.2))` times `LFunction (fixedSourcePrincipal S _) (υ+i p.2)` is integrable for `heightMeasure`.
--
--   Lean: `OAI.SevenEighths.ProbePrincipalContours.continued_source_joint_integrable` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

local instance instCountableO_r722ab9_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_r722ab9_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
theorem continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  sorry

end SevenEighths.ProbePrincipalContours
end

end OAI
end
