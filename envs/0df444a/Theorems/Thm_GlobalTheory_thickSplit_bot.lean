-- Prove2me | Theorems.Thm_GlobalTheory_thickSplit_bot
-- name    : GlobalTheory.thickSplit_bot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:02:58.988801+00:00
-- url     : https://prove2.me/theorems/ae179e60-eff3-4342-ae77-d30cd58ad815
-- title:
--   Global Theory: thick Split bot
-- statement:
--   The Global Theory construction uses the thick Split bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ThickSplitRealSpanBot.lean#L18-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ThickSplitRealSpanBot.lean#L18-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ThickSplitRealSpanBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
noncomputable section

theorem GlobalTheory.thickSplit_bot :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF),
      ¬ X.la1 < P.th → IsSplit P ⊥ := by sorry
