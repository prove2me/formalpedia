-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_norm_unit_zpow_sub_one
-- name    : GlobalTheory.Cyc.norm_unit_zpow_sub_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:39.133798+00:00
-- url     : https://prove2.me/theorems/5021f9a7-8b9c-4361-9434-d595cb4e70cc
-- title:
--   Cyc: norm unit zpow sub one
-- statement:
--   The Cyc construction uses the norm unit zpow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L96-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L96-L119

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.Cyc.norm_unit_zpow_sub_one :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (s : ℕ) (u : ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) →
      ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) → ∀ n : ℤ, n ≠ 0 →
      ‖((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) * ‖(n : ℤ_[l])‖ := by sorry
