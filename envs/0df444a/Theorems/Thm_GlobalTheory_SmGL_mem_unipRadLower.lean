-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_mem_unipRadLower
-- name    : GlobalTheory.SmGL.mem_unipRadLower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:34.089944+00:00
-- url     : https://prove2.me/theorems/0dfbd91b-2a7b-49be-a759-f952dbc2694d
-- title:
--   Sm GL: mem unip Rad Lower
-- statement:
--   The Sm GL construction uses the mem unip Rad Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L435-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L435-L439

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

theorem GlobalTheory.SmGL.mem_unipRadLower {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.unipRadLower R e ↔ g ∈ _root_.GlobalTheory.SmGL.parabLower R e ∧
      ∀ a (i j : m a),
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j := by sorry
