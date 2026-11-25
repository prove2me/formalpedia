-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_inhabited_setting
-- name    : GlobalTheory.K5.Basic.inhabited_setting
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:44.819307+00:00
-- url     : https://prove2.me/theorems/62825129-3add-4489-a01e-b2db14693de0
-- title:
--   Basic: inhabited setting
-- statement:
--   The Basic construction uses the inhabited setting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L545-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L545-L552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial

theorem GlobalTheory.K5.Basic.inhabited_setting (p : ℕ) [Fact p.Prime] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (O0 p) Ω), IsClo p Ω ∧ ∃ T : Tower p Ω,
      ∀ n, (∃ ι, IsEmb T n ι) ∧
        (∃ χ : Gal p Ω → ZMod (p ^ n), ∀ g : Gal p Ω, g (T.ζ n) = T.ζ n ^ (χ g).val) ∧
        ∃ a, IsKum T n ⊤ (T.qq n) a := by sorry
