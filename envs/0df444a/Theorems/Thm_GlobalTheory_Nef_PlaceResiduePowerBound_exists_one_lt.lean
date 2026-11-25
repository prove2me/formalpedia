-- Prove2me | Theorems.Thm_GlobalTheory_Nef_PlaceResiduePowerBound_exists_one_lt
-- name    : GlobalTheory.Nef.PlaceResiduePowerBound.exists_one_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:35.035131+00:00
-- url     : https://prove2.me/theorems/d6a30fe4-01f0-448b-afe4-70980f8a5891
-- title:
--   Place Residue Power Bound: exists one lt
-- statement:
--   The Place Residue Power Bound construction uses the exists one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceRestrictionExistsPow.lean#L120-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceRestrictionExistsPow.lean#L120-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PlaceResiduePowerBound
open WithZero
variable {F : Type} [Field F]

theorem GlobalTheory.Nef.PlaceResiduePowerBound.exists_one_lt {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : Valuation E ℤᵐ⁰) (hp : Function.Surjective p) : ∃ a : F, 1 < p (algebraMap F E a) := by sorry
