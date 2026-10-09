-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_residue_iterated_integrable
-- name    : OAI.SevenEighths.ProbePrincipalContours.residue_iterated_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:03:16.614692+00:00
-- url     : https://prove2.me/theorems/85f873c1-5362-42d8-9a78-b71caa4e7197
-- title:
--   Integrability of the iterated residue integral
-- statement:
--   With $\eta,S,J,T,b,W_0,W_1,a_0,b_0,a_1,b_1$ as in the other principal-contour statements (`SourceExclusions S`, the $T_j$ avoiding $S$, $W_k$ Schwartz with support in $[a_k,b_k]$, $a_k>0$), reals $X,Z>0$, $Y$, $a\ge7/8$ with `beta` $<a$ and $\xi\ge33/200$ with $6\xi\ne1$: the function $t\mapsto$`verticalIntegral ξ` of $z\mapsto$`sourceMultiplier W0 W1 X Y Z (η.excludePrimes S _) (a+it) (globalClosedCorrection η S (a+it)) (slotMultiplier η J T b (a+it)) 1 z`·`LFunction (fixedSourcePrincipal S _) (6z)` is integrable on $\mathbb R$.
--
--   Lean: `OAI.SevenEighths.ProbePrincipalContours.residue_iterated_integrable` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

local instance instCountableO_re17a54_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_re17a54_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
theorem residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z))) := by
  sorry

end SevenEighths.ProbePrincipalContours
end

end OAI
end
