-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_source_iterated_integrable
-- name    : OAI.SevenEighths.ProbePrincipalContours.source_iterated_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:07:47.396757+00:00
-- url     : https://prove2.me/theorems/9bc5dbb9-8984-4de4-8dde-34c7487ea906
-- title:
--   Integrability of the iterated source integral
-- statement:
--   With the same data, reals $X,Y,Z>0$, $a\ge7/8$ with `beta` $<a$, $\xi\ge33/200$ with $6\xi\ne1$, $c_w>1$ and $\upsilon\in[19/20,c_w]$, $\upsilon\ne1$: the function $t\mapsto$`verticalIntegral ξ` of $z\mapsto$`verticalIntegral υ` of $w\mapsto$`sourceMultiplier … (a+it) … w z`·`LFunction π (6z)`·`LFunction π w` (with $\pi=$`fixedSourcePrincipal S _`) is integrable on $\mathbb R$.
--
--   Lean: `OAI.SevenEighths.ProbePrincipalContours.source_iterated_integrable` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

local instance instCountableO_r6e61c8_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_r6e61c8_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
theorem source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  sorry

end SevenEighths.ProbePrincipalContours
end

end OAI
end
