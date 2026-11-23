-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_det_leviEmb
-- name    : GlobalTheory.SmGL.det_leviEmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:15.203296+00:00
-- url     : https://prove2.me/theorems/47d0b2ef-83d5-4766-a970-8c52eb27b649
-- title:
--   Sm GL: det levi Emb
-- statement:
--   The Sm GL construction uses the det levi Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L214-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L214-L222

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
omit [LinearOrder α]

theorem GlobalTheory.SmGL.det_leviEmb (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.leviEmb R e g) =
      ∏ a, GeneralLinearGroup.det (g a) := by sorry
