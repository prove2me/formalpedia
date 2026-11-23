-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_norm_nat_sub_one_le_iff
-- name    : GlobalTheory.Cyc.norm_nat_sub_one_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:00.361808+00:00
-- url     : https://prove2.me/theorems/1c2f677a-48b0-49b4-b765-f81cf47739e3
-- title:
--   Cyc: norm nat sub one le iff
-- statement:
--   The Cyc construction uses the norm nat sub one le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L22-L26

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
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

theorem GlobalTheory.Cyc.norm_nat_sub_one_le_iff (a m : ℕ) :
    ‖(a : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ↔ ((l : ℤ) ^ m) ∣ (a : ℤ) - 1 := by sorry
