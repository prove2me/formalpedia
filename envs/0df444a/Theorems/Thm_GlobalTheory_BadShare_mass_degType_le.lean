-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_mass_degType_le
-- name    : GlobalTheory.BadShare.mass_degType_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:12:25.603675+00:00
-- url     : https://prove2.me/theorems/6569d992-f3dd-451c-afc2-cfbb4d5f81d1
-- title:
--   Bad Share: mass deg Type le
-- statement:
--   The Bad Share construction uses the mass deg Type le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelMassDegreeTypeLe.lean#L230-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelMassDegreeTypeLe.lean#L230-L263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusCardBoundsAndMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelMassDegreeTypeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.BadShare
open Polynomial Classical UniqueFactorizationMonoid

theorem GlobalTheory.BadShare.mass_degType_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (μ : Multiset ℕ),
    (_root_.GlobalTheory.BadShare.mass g N fun f => _root_.GlobalTheory.BadShare.degType g f = μ) ≤
      (∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * (μ.count d).factorial))⁻¹ := by sorry
