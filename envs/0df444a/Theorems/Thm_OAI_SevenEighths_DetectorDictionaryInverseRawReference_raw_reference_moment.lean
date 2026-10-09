-- Prove2me | Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseRawReference_raw_reference_moment
-- name    : OAI.SevenEighths.DetectorDictionaryInverseRawReference.raw_reference_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:07:16.367246+00:00
-- url     : https://prove2.me/theorems/788870b5-2367-4249-a7b5-bb596ba18606
-- title:
--   Raw moments for child log tests
-- statement:
--   Let $W$ be Schwartz with support in $[a,b]$, $a,b>0$, and $c,\kappa>0$. Then there is $J$ such that for every `RowData` there is $C>0$ with `RawMoment data (childLogTest W t) c κ (C(1+|t|)^{2J})` for every real $t$.
--
--   Lean: `OAI.SevenEighths.DetectorDictionaryInverseRawReference.raw_reference_moment` in `lean/OAI/NumberTheory/DirichletL/Dictionary/InverseRawReference.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialExcludedPeriod
open InverseInitialRayAttachment InverseInitialProfileBounds
open DetectorDictionaryInverseRawRealRadial
open DetectorDictionaryInverseRawGeometry IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem raw_reference_moment (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧ ∀t:ℝ,
      RawMoment data (childLogTest W t) c κ (C*(1+‖t‖)^(2*J)) := by
  sorry

end SevenEighths.DetectorDictionaryInverseRawReference

end

end OAI
end
