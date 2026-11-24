-- Prove2me | Theorems.Thm_GlobalTheory_TargetEquivalence_main
-- name    : GlobalTheory.TargetEquivalence.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:59.689603+00:00
-- url     : https://prove2.me/theorems/db63667f-c15f-4942-abf8-790f9aa96b58
-- title:
--   Target Equivalence: main
-- statement:
--   The Target Equivalence construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreFurther.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreFurther.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetEquivalence
open Finset

theorem GlobalTheory.TargetEquivalence.main {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by sorry
