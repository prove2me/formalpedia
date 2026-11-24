-- Prove2me | Theorems.Thm_GlobalTheory_GradedFixed_WA_union
-- name    : GlobalTheory.GradedFixed.WA_union
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:47.5108+00:00
-- url     : https://prove2.me/theorems/c39d1459-8982-45cc-88e6-f190d6e9571d
-- title:
--   Graded Fixed: WA union
-- statement:
--   The Graded Fixed construction uses the WA union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L17-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.GradedFixed.WA_union (V : ι → Submodule ℂ M) (A B : Set ι) : WA V (A ∪ B) = WA V A ⊔ WA V B := by sorry
