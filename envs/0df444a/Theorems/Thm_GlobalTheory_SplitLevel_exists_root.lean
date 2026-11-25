-- Prove2me | Theorems.Thm_GlobalTheory_SplitLevel_exists_root
-- name    : GlobalTheory.SplitLevel.exists_root
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:44.962056+00:00
-- url     : https://prove2.me/theorems/828b6442-8cfe-423b-983a-9734790e1a92
-- title:
--   Split Level: exists root
-- statement:
--   The Split Level construction uses the exists root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLevelMulSplit.lean#L11-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLevelMulSplit.lean#L11-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLevelMulSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.SplitLevel

theorem GlobalTheory.SplitLevel.exists_root {p d m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 4 * m = d + 1)
    (hj : jacobiSym (-(d : ℤ)) p = 1) :
    ∃ c : ℤ, (p : ℤ) ∣ c ^ 2 - c + m ∧ IsCoprime (1 - 2 * c) (p : ℤ) := by sorry
