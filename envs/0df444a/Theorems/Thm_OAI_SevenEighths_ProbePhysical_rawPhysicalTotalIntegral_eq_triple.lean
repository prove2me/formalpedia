-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_rawPhysicalTotalIntegral_eq_triple
-- name    : OAI.SevenEighths.ProbePhysical.rawPhysicalTotalIntegral_eq_triple
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:33.804256+00:00
-- url     : https://prove2.me/theorems/5e85cfa3-027b-4cf4-baf9-0fb277efc00d
-- title:
--   The raw physical total integral equals the raw source triple integral
-- statement:
--   For the same data: `rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z` $=$ `rawSourceTripleIntegral η S hS D W0 W1 X Y Z`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.rawPhysicalTotalIntegral_eq_triple` in `lean/OAI/NumberTheory/DirichletL/Detector/RawSourceIntegral.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

local instance instCountableO_5_r74ba4a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_5_r74ba4a_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
attribute [local instance] OAI.SevenEighths.ProbePhysical.instMeasurableSpaceSourceRawIndex_2
local instance instMeasurableSingletonClassSourceRawIndex_2_r74ba4a_1 (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩
lemma rawPhysicalTotalIntegral_eq_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      rawSourceTripleIntegral η S hS D W0 W1 X Y Z := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
