-- Prove2me | Theorems.Thm_GlobalTheory_FrameNet_cell_mem
-- name    : GlobalTheory.FrameNet.cell_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:38.493257+00:00
-- url     : https://prove2.me/theorems/f444a050-b18e-49a0-8e16-2a1d327e50e8
-- title:
--   Frame Net: cell mem
-- statement:
--   The Frame Net construction uses the cell mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L91-L95

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

theorem GlobalTheory.FrameNet.cell_mem {s δ : ℝ} (hδ : 0 < δ) {z : ℂ} (h : ‖z‖ ≤ s) :
    cell s δ z ∈ Finset.Icc (0 : ℤ) ⌊2 * s / δ⌋ ×ˢ Finset.Icc (0 : ℤ) ⌊2 * s / δ⌋ := by sorry
