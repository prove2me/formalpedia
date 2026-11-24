-- Prove2me | Theorems.Thm_GlobalTheory_FrameNet_log_le_of_card_le
-- name    : GlobalTheory.FrameNet.log_le_of_card_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:37:18.451894+00:00
-- url     : https://prove2.me/theorems/17b6821f-cd11-4d9c-857c-7e29fbdb3937
-- title:
--   Frame Net: log le of card le
-- statement:
--   The Frame Net construction uses the log le of card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L449-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L449-L484

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem GlobalTheory.FrameNet.log_le_of_card_le {n f r : ℕ} {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η) (hη : η ≤ 1)
    (h : (n : ℝ) ≤ (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * f * r ^ 2)) :
    (n : ℝ) ≤ Real.exp (2 * f * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * f * (r : ℝ) ^ 3 * Real.log (r * B)) ∧
      Real.log n ≤ 2 * f * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * f * (r : ℝ) ^ 3 * Real.log (r * B) := by sorry
