-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCover_exists_denominator
-- name    : GlobalTheory.FiniteCover.exists_denominator
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:29:56.06713+00:00
-- url     : https://prove2.me/theorems/555d00c4-acfa-49d7-93ef-bab62cd8de33
-- title:
--   Finite Cover: exists denominator
-- statement:
--   The Finite Cover construction uses the exists denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCommonMultiple.lean#L16-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCommonMultiple.lean#L16-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.FiniteCover

theorem GlobalTheory.FiniteCover.exists_denominator {A C F F' ι : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field F] [Field F'] [Algebra A C] [Module.Finite A C] [Algebra A F] [IsFractionRing A F]
    [Algebra C F'] [IsFractionRing C F'] [Algebra F F'] [Algebra A F'] [IsScalarTower A F F']
    [IsScalarTower A C F'] [Fintype ι] (e : Basis ι F F') :
    ∃ c : A, c ≠ 0 ∧
      (∀ j (y : C), ∃ a : A, algebraMap A F a = algebraMap A F c * e.repr (algebraMap C F' y) j) ∧
      ∀ j, ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by sorry
