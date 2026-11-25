-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_flatOf_apply
-- name    : GlobalTheory.Doubling.flatOf_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:10:37.15834+00:00
-- url     : https://prove2.me/theorems/34301dc6-b0dd-5e4f-8db7-fe29d182ad71
-- title:
--   Doubling: flat Of apply
-- statement:
--   The Doubling construction uses the flat Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L482-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L482-L483

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
open scoped NNReal
open MeasureTheory
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A) (ν : Aˣ →* ℝ≥0) (K : Subgroup G)
variable {e mat ν K}

theorem GlobalTheory.Doubling.flatOf_apply (Φ : G → ℂ) (s₀ s : ℂ) (g : G) :
    flatOf e mat ν K Φ s₀ s g = Φ g * npow (hgtOf e mat ν K g) (s - s₀) := by sorry
