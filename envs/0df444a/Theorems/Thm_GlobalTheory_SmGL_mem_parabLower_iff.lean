-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_mem_parabLower_iff
-- name    : GlobalTheory.SmGL.mem_parabLower_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:17.854372+00:00
-- url     : https://prove2.me/theorems/1a360d0e-adc1-4f63-aaf0-5fc04905228d
-- title:
--   Sm GL: mem parab Lower iff
-- statement:
--   The Sm GL construction uses the mem parab Lower iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L410-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L410-L419

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
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem GlobalTheory.SmGL.mem_parabLower_iff {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parabLower R e ↔ ∀ a b (i : m a) (j : m b), a < b →
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by sorry
