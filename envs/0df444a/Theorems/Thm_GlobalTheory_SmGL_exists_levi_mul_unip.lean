-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_exists_levi_mul_unip
-- name    : GlobalTheory.SmGL.exists_levi_mul_unip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:12.13219+00:00
-- url     : https://prove2.me/theorems/957aca79-8eb7-4db7-a8ea-8e2d0b195a85
-- title:
--   Sm GL: exists levi mul unip
-- statement:
--   The Sm GL construction uses the exists levi mul unip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L340-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L340-L351

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

theorem GlobalTheory.SmGL.exists_levi_mul_unip (e : (Σ a, m a) ≃ n)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    ∃ u ∈ _root_.GlobalTheory.SmGL.unipRad R e,
      (p : GL n R) = _root_.GlobalTheory.SmGL.leviEmb R e (_root_.GlobalTheory.SmGL.leviProj R e p) * u := by sorry
