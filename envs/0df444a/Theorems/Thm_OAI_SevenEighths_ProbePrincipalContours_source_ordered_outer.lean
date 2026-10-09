-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_source_ordered_outer
-- name    : OAI.SevenEighths.ProbePrincipalContours.source_ordered_outer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:11:53.407618+00:00
-- url     : https://prove2.me/theorems/50528054-4ec6-43ab-888b-a42fdcd25b69
-- title:
--   Moving the w and z contours of the source integral
-- statement:
--   With the same data, reals $X,Y,Z>0$, $a\ge7/8$ with `beta` $<a$, $c_w>1$ and $e>0$, write $K(s)$ for `sourceMultiplier W0 W1 X Y Z (η.excludePrimes S _) s (globalClosedCorrection η S s) (slotMultiplier η J T b s)`, $\pi=$`fixedSourcePrincipal S _` and $R=$`HeckeReciprocal.regularizedL π 1`. Then, with $\int_c$ denoting `verticalIntegral c`,
--   $$\int_a\!\int_{1/6+e}\!\int_{c_w}K(s)(w,z)L(\pi,6z)L(\pi,w)=\int_a\!\int_{1/6+e}\!\int_{19/20}K(s)(w,z)L(\pi,6z)L(\pi,w)+R\int_a\!\int_{33/200}K(s)(1,z)L(\pi,6z)+\frac{R^2}6\int_aK(s)(1,1/6).$$
--
--   Lean: `OAI.SevenEighths.ProbePrincipalContours.source_ordered_outer` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B021

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

local instance instCountableO_r871faa_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_r871faa_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
theorem source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  sorry

end SevenEighths.ProbePrincipalContours
end

end OAI
end
