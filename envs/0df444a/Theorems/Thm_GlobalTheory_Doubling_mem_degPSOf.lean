-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_mem_degPSOf
-- name    : GlobalTheory.Doubling.mem_degPSOf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:44.481628+00:00
-- url     : https://prove2.me/theorems/61f2b7c6-1af5-48e8-8a94-dbdb4f0a8b7c
-- title:
--   Doubling: mem deg PSOf
-- statement:
--   The Doubling construction uses the mem deg PSOf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L477-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L477-L480

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

theorem GlobalTheory.Doubling.mem_degPSOf [TopologicalSpace G] {μ : Aˣ →* Circle} {s : ℂ} {Φ : G → ℂ} : Φ ∈ degPSOf e mat ν K μ s ↔
    (∀ (p : siegelOf e mat) (g : G),
      Φ (p * g) = μ (aOf e mat p) * npow (ν (aOf e mat p)) (s + (Fintype.card n : ℂ) / 2) * Φ g) ∧
      Continuous Φ ∧ IsKFinite K Φ := by sorry
