-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_exists_norm_sub_pow_le
-- name    : GlobalTheory.Cyc.exists_norm_sub_pow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:04:59.21848+00:00
-- url     : https://prove2.me/theorems/413c9d8f-ece5-478f-8115-65969c5e7f69
-- title:
--   Cyc: exists norm sub pow le
-- statement:
--   The Cyc construction uses the exists norm sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicTowerLevelGeneratorProperties.lean#L41-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicTowerLevelGeneratorProperties.lean#L41-L78

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

theorem GlobalTheory.Cyc.exists_norm_sub_pow_le (j : ℕ) (hj : Lev l j) (u s : ℚ_[l]) (hu1 : ‖u‖ = 1)
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (hs : ‖s - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) (m : ℕ) :
    ∃ a : ℕ, ‖s - u ^ a‖ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by sorry
