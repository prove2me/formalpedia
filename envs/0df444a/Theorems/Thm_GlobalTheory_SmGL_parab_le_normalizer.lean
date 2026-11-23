-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_parab_le_normalizer
-- name    : GlobalTheory.SmGL.parab_le_normalizer
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:29.116158+00:00
-- url     : https://prove2.me/theorems/82fa27ea-6e04-4fd8-8dcb-3eafeb7e02a1
-- title:
--   Sm GL: parab le normalizer
-- statement:
--   The Sm GL construction uses the parab le normalizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L305-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L305-L315

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

theorem GlobalTheory.SmGL.parab_le_normalizer (e : (Σ a, m a) ≃ n) :
    _root_.GlobalTheory.SmGL.parab R e ≤
      Subgroup.normalizer (_root_.GlobalTheory.SmGL.unipRad R e : Set (GL n R)) := by sorry
