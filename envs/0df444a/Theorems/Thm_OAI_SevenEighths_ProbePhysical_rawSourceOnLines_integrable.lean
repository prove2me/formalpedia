-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_rawSourceOnLines_integrable
-- name    : OAI.SevenEighths.ProbePhysical.rawSourceOnLines_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:44.830621+00:00
-- url     : https://prove2.me/theorems/4aee7eb9-675f-4934-8d59-47045aafb3d8
-- title:
--   Integrability of raw source values on lines
-- statement:
--   For $\eta$, a finite set $S$ of maximal ideals, an ideal $D$, Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$) and $X,Y,Z>0$: $(p_1,p_2)\mapsto$`rawSourceOnLines η S hS D W0 W1 X Y Z p₁ p₂` is integrable for counting measure on `SourceRawIndex S` times `heightMeasure`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.rawSourceOnLines_integrable` in `lean/OAI/NumberTheory/DirichletL/Detector/RawSourceIntegral.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

local instance instCountableO_5_rb418a0_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_5_rb418a0_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
attribute [local instance] OAI.SevenEighths.ProbePhysical.instMeasurableSpaceSourceRawIndex_2
local instance instMeasurableSingletonClassSourceRawIndex_2_rb418a0_1 (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩
lemma rawSourceOnLines_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=>rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
