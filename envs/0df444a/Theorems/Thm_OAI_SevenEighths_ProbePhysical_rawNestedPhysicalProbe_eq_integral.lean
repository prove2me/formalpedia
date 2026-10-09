-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_rawNestedPhysicalProbe_eq_integral
-- name    : OAI.SevenEighths.ProbePhysical.rawNestedPhysicalProbe_eq_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:46.330311+00:00
-- url     : https://prove2.me/theorems/77d0b578-e441-4bfe-a0dc-ae5c2745ebda
-- title:
--   The raw nested physical probe equals the raw total integral
-- statement:
--   For $\eta$, a nonempty finite set $S$ of maximal prime ideals containing `fixedBadPrimes`, an ideal $D$, Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$) and $X,Y,Z>0$: `rawNestedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z 2 3` $=$ `rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.rawNestedPhysicalProbe_eq_integral` in `lean/OAI/NumberTheory/DirichletL/Detector/PhysicalRawIntegral.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

local instance instCountableO_4_r7f0d3b_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_4_r7f0d3b_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance instMeasurableSpaceO_1_r7f0d3b_1 : MeasurableSpace O := ⊤
local instance instMeasurableSingletonClassO_1_r7f0d3b_1 : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance instMeasurableSpaceIdealO_1_r7f0d3b_1 : MeasurableSpace (Ideal O) := ⊤
local instance instMeasurableSingletonClassIdealO_1_r7f0d3b_1 : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩
attribute [local instance] OAI.SevenEighths.ProbePhysical.instMeasurableSpaceSourceRawIndex_1
local instance instMeasurableSingletonClassSourceRawIndex_1_r7f0d3b_1 (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩
theorem rawNestedPhysicalProbe_eq_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawNestedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z 2 3=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
