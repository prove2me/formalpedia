-- Prove2me | Theorems.Thm_Neutral_B1_isFiniteAbelian_bot
-- name    : Neutral.B1.isFiniteAbelian_bot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:41.558027+00:00
-- url     : https://prove2.me/theorems/badb9551-56f8-491e-b226-963874972981
-- title:
--   B1: is Finite Abelian bot
-- statement:
--   The B1 construction uses the is Finite Abelian bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L18-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (F : Type*) [Field F]

theorem Neutral.B1.isFiniteAbelian_bot : IsFiniteAbelian F (⊥ : IntermediateField F (AlgebraicClosure F)) := by sorry
