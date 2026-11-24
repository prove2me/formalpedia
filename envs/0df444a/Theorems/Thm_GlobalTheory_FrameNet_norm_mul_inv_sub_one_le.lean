-- Prove2me | Theorems.Thm_GlobalTheory_FrameNet_norm_mul_inv_sub_one_le
-- name    : GlobalTheory.FrameNet.norm_mul_inv_sub_one_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:37:43.943252+00:00
-- url     : https://prove2.me/theorems/ca65865c-ab0e-4e0f-a4fc-0e73d5d47bd1
-- title:
--   Frame Net: norm mul inv sub one le
-- statement:
--   The Frame Net construction uses the norm mul inv sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L33-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L33-L64

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

theorem GlobalTheory.FrameNet.norm_mul_inv_sub_one_le {r : ℕ} {m m' : Matrix (Fin r) (Fin r) ℂ} {s ε : ℝ} (hs : 1 ≤ s)
    (hm : ∀ i k, ‖m' i k‖ ≤ s) (hd : m'.det ≠ 0) (hε : ∀ i k, ‖m i k - m' i k‖ ≤ ε) (a b : Fin r) :
    ‖(m * m'⁻¹) a b - (if a = b then 1 else 0)‖ ≤ r * (ε * ((r : ℝ) ^ r * s ^ r / ‖m'.det‖)) := by sorry
