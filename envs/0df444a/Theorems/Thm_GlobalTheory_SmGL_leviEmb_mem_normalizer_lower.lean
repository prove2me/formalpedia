-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_normalizer_lower
-- name    : GlobalTheory.SmGL.leviEmb_mem_normalizer_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:25.149796+00:00
-- url     : https://prove2.me/theorems/f25a2cf0-2fc2-4d1e-82f5-e8c13e2ee918
-- title:
--   Sm GL: levi Emb mem normalizer lower
-- statement:
--   The Sm GL construction uses the levi Emb mem normalizer lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L463-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L463-L468

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

theorem GlobalTheory.SmGL.leviEmb_mem_normalizer_lower (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviEmb R e g ∈
      Subgroup.normalizer (_root_.GlobalTheory.SmGL.unipRadLower R e : Set (GL n R)) := by sorry
