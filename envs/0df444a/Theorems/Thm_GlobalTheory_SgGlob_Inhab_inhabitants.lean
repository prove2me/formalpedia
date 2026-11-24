-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_inhabitants
-- name    : GlobalTheory.SgGlob.Inhab.inhabitants
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:24.994102+00:00
-- url     : https://prove2.me/theorems/60e5c30f-c709-417c-b9d2-e4fd6f5e1845
-- title:
--   Inhab: inhabitants
-- statement:
--   The Inhab construction uses the inhabitants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L426-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L426-L445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.SgGlob.Inhab.inhabitants (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    (IsHermU σ (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) E) ∧
      ((Submodule.span (𝓞 E) {![0, 1], ![1, 1]}, !![0; 1], !![(g : E); 1 + g]) : Tri E 2 0) ∈
        GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ∧
      Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] = (g : E) ^ 2) ∧
    ((Submodule.span (𝓞 E) {![0, 1], ![1, 1]}, ![0, 1]) ∈ LzSet σ !![1, 0; 0, -1] (1 : E)) ∧
    ((∀ x, σ (σ x) = x) → IsHermU σ (splitJ E) ∧
      ∃ (Q : Matrix (Fin 8) (Fin (1 + 1)) E) (Z : Matrix (Fin (1 + 1)) (Fin (1 + 1)) E),
        ((splitLat E, splitP E, Q) : Tri E 8 1) ∈ GenConf σ (splitJ E) 1 (1 + 2 * g) g Z ∧
        ((∃ τ : E →+* ℂ, ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) → Gq σ 1 (1 + 2 * g) Z ≠ 0)) ∧
    Mass (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ≠ 0 := by sorry
