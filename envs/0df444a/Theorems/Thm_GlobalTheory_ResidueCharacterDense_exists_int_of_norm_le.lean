-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_exists_int_of_norm_le
-- name    : GlobalTheory.ResidueCharacterDense.exists_int_of_norm_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:35:06.674384+00:00
-- url     : https://prove2.me/theorems/d1c1bd5c-b285-4f2a-add8-ab224a744d4b
-- title:
--   Residue Character Dense: exists int of norm le
-- statement:
--   The Residue Character Dense construction uses the exists int of norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L56-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L56-L70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense

theorem GlobalTheory.ResidueCharacterDense.exists_int_of_norm_le {l : ℕ} [Fact l.Prime] (q : ℚ) (n : ℕ) (m : ℤ)
    (h : q * (l : ℚ) ^ n = m) (hq : ‖(q : ℚ_[l])‖ ≤ 1) : ∃ c : ℤ, q = c := by sorry
