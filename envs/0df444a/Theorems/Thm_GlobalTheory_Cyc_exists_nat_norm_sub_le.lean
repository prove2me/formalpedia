-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_exists_nat_norm_sub_le
-- name    : GlobalTheory.Cyc.exists_nat_norm_sub_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:23.701508+00:00
-- url     : https://prove2.me/theorems/d569da0e-8937-4cb0-8ea1-c47354affc56
-- title:
--   Cyc: exists nat norm sub le
-- statement:
--   The Cyc construction uses the exists nat norm sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicTowerLevelGeneratorProperties.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicTowerLevelGeneratorProperties.lean#L25-L31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.exists_nat_norm_sub_le (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) :
    ∃ k : ℕ, ‖x - k‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by sorry
