-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_exists_three
-- name    : GlobalTheory.LocalQuad.FiveVar.exists_three
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:13:27.409336+00:00
-- url     : https://prove2.me/theorems/6d6304ab-47fc-4fb6-9e07-235b1d4081d7
-- title:
--   Five Var: exists three
-- statement:
--   The Five Var construction uses the exists three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L193-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L193-L196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
variable [DecidableEq n]

theorem GlobalTheory.LocalQuad.FiveVar.exists_three (f : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f j = f i ∧ f k = f i := by sorry
