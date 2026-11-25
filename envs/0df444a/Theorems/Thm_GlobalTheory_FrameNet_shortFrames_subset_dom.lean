-- Prove2me | Theorems.Thm_GlobalTheory_FrameNet_shortFrames_subset_dom
-- name    : GlobalTheory.FrameNet.shortFrames_subset_dom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:50.93019+00:00
-- url     : https://prove2.me/theorems/596a3d3c-d9f2-4cc2-b1b7-a0479bdda069
-- title:
--   Frame Net: short Frames subset dom
-- statement:
--   The Frame Net construction uses the short Frames subset dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L346-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L346-L365

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

theorem GlobalTheory.FrameNet.shortFrames_subset_dom (v : Fin r → Fin r → E) (B : ℝ) : shortFrames X v B ⊆ X.dom := by sorry
