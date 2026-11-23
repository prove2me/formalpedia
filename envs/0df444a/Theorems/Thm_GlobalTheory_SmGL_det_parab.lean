-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_det_parab
-- name    : GlobalTheory.SmGL.det_parab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:06.209406+00:00
-- url     : https://prove2.me/theorems/f34a3fa4-06b5-425d-a484-eb9b3db1aa7c
-- title:
--   Sm GL: det parab
-- statement:
--   The Sm GL construction uses the det parab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L195-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L195-L205

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
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)

theorem GlobalTheory.SmGL.det_parab (e : (Σ a, m a) ≃ n)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    GeneralLinearGroup.det (p : GL n R) =
      ∏ a, GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.leviProj R e p a) := by sorry
