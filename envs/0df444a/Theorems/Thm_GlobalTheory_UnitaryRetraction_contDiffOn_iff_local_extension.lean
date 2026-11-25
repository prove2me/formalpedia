-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryRetraction_contDiffOn_iff_local_extension
-- name    : GlobalTheory.UnitaryRetraction.contDiffOn_iff_local_extension
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:38.889245+00:00
-- url     : https://prove2.me/theorems/42a6bcd9-4b04-45b5-9bae-0f50b877ef09
-- title:
--   Unitary Retraction: cont Diff On iff local extension
-- statement:
--   The Unitary Retraction construction uses the cont Diff On iff local extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ContDiffOnIffLocalExtension.lean#L237-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ContDiffOnIffLocalExtension.lean#L237-L300

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ContDiffOnIffLocalExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.UnitaryRetraction
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {H : Matrix (Fin n) (Fin n) ℂ}
open Matrix
open scoped ContDiff
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {H : Matrix (Fin n) (Fin n) ℂ}

theorem GlobalTheory.UnitaryRetraction.contDiffOn_iff_local_extension (hH : Hᴴ = H) (h2 : H * H = 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Matrix (Fin n) (Fin n) ℂ → E) :
    ContDiffOn ℝ ∞ f {g | gᴴ * H * g = H} ↔
      ∀ g₀, g₀ᴴ * H * g₀ = H → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ))
        (F : Matrix (Fin n) (Fin n) ℂ → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
          ∀ g ∈ U, gᴴ * H * g = H → f g = F g := by sorry
