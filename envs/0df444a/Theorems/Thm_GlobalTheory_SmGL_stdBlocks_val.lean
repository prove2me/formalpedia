-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_stdBlocks_val
-- name    : GlobalTheory.SmGL.stdBlocks_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:56.481802+00:00
-- url     : https://prove2.me/theorems/c01cc4ac-3240-4b65-8fa9-fde98da4e2a7
-- title:
--   Sm GL: std Blocks val
-- statement:
--   The Sm GL construction uses the std Blocks val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L481-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L481-L485

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)

theorem GlobalTheory.SmGL.stdBlocks_val {s N : ℕ} (d : Fin s → ℕ) (h : ∑ a, d a = N)
    (a : Fin s) (i : Fin (d a)) :
    (_root_.GlobalTheory.SmGL.stdBlocks d h ⟨a, i⟩ : ℕ) =
      ∑ b : Fin a, d (Fin.castLE a.2.le b) + i := by sorry
