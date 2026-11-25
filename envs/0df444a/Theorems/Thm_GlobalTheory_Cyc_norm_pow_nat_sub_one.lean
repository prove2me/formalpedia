-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_norm_pow_nat_sub_one
-- name    : GlobalTheory.Cyc.norm_pow_nat_sub_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:56:09.368573+00:00
-- url     : https://prove2.me/theorems/0e1c0468-b93d-437f-bf88-e1770378939d
-- title:
--   Cyc: norm pow nat sub one
-- statement:
--   The Cyc construction uses the norm pow nat sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L71-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L71-L94

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

theorem GlobalTheory.Cyc.norm_pow_nat_sub_one (n : ℕ) (hn : n ≠ 0) : ∀ (x : ℤ_[l]), ‖x - 1‖ ≤ (l : ℝ)⁻¹ →
    (l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) → ‖x ^ n - 1‖ = ‖x - 1‖ * ‖(n : ℤ_[l])‖ := by sorry
