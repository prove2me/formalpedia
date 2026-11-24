-- Prove2me | Theorems.Thm_GlobalTheory_FrameNet_exists_net_card_le
-- name    : GlobalTheory.FrameNet.exists_net_card_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:38:23.708168+00:00
-- url     : https://prove2.me/theorems/31a3b837-c457-49b3-8b7a-ccf28cbb620d
-- title:
--   Frame Net: exists net card le
-- statement:
--   The Frame Net construction uses the exists net card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L367-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L367-L447

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

theorem GlobalTheory.FrameNet.exists_net_card_le (v : Fin r → Fin r → E) (hv : LinearIndependent E v)
    (hint : ∀ i k, IsIntegral ℤ (herm X.Gm (v i) (v k))) {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η)
    (hη : η ≤ 1) :
    ∃ N : Finset (Frame X.Ψ r), (N : Set (Frame X.Ψ r)) ⊆ shortFrames X v B ∧
      (∀ x ∈ shortFrames X v B, ∃ A : Frame X.Ψ r, rmul x A ∈ N ∧
        ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ η) ∧
      (N.card : ℝ) ≤ (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * fdeg E * r ^ 2) := by sorry
