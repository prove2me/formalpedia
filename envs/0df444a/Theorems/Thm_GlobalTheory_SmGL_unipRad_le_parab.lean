-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_unipRad_le_parab
-- name    : GlobalTheory.SmGL.unipRad_le_parab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:29.944265+00:00
-- url     : https://prove2.me/theorems/1b08f22f-6ff3-4f69-9582-86560e655d38
-- title:
--   Sm GL: unip Rad le parab
-- statement:
--   The Sm GL construction uses the unip Rad le parab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L261-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L261-L263

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

theorem GlobalTheory.SmGL.unipRad_le_parab (e : (Σ a, m a) ≃ n) :
    _root_.GlobalTheory.SmGL.unipRad R e ≤ _root_.GlobalTheory.SmGL.parab R e := by sorry
