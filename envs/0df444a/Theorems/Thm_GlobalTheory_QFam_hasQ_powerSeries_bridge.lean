-- Prove2me | Theorems.Thm_GlobalTheory_QFam_hasQ_powerSeries_bridge
-- name    : GlobalTheory.QFam.hasQ_powerSeries_bridge
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:33.034796+00:00
-- url     : https://prove2.me/theorems/8bee344d-17d2-4ca0-9a9b-c078f93530ea
-- title:
--   QFam: has Q power Series bridge
-- statement:
--   The QFam construction uses the has Q power Series bridge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQCoeffIffHasQExpansion.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQCoeffIffHasQExpansion.lean#L24-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.hasQ_powerSeries_bridge :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ),
      HasQ N f a ↔ GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk a)) ∧
    (∀ (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ),
      HasQ N f (fun n => PowerSeries.coeff n φ) ↔ GlobalTheory.HasQExpansion (N : ℝ) f φ) := by sorry
