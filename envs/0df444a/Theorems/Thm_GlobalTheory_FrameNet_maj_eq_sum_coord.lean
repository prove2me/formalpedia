-- Prove2me | Theorems.Thm_GlobalTheory_FrameNet_maj_eq_sum_coord
-- name    : GlobalTheory.FrameNet.maj_eq_sum_coord
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:37:25.410925+00:00
-- url     : https://prove2.me/theorems/e11c6e54-e096-4489-9f32-58faae236f43
-- title:
--   Frame Net: maj eq sum coord
-- statement:
--   The Frame Net construction uses the maj eq sum coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L320-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L320-L333

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

theorem GlobalTheory.FrameNet.maj_eq_sum_coord {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → Fin r → E)
    (k : Fin r) : X.maj x τ (Data.emb τ.1 (v k)) =
      ∑ i, ‖((mat x τ)⁻¹ * basisMat τ.1 v) i k‖ ^ 2 := by sorry
