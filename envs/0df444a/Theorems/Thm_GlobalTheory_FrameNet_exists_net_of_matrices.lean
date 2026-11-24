-- Prove2me | Theorems.Thm_GlobalTheory_FrameNet_exists_net_of_matrices
-- name    : GlobalTheory.FrameNet.exists_net_of_matrices
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:53.429951+00:00
-- url     : https://prove2.me/theorems/be3856b8-02f8-40f7-9b46-a4287282ea71
-- title:
--   Frame Net: exists net of matrices
-- statement:
--   The Frame Net construction uses the exists net of matrices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L125-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean#L125-L238

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

theorem GlobalTheory.FrameNet.exists_net_of_matrices {α ι : Type*} [Fintype ι] {r : ℕ} (O : Set α)
    (m : α → ι → Matrix (Fin r) (Fin r) ℂ) (D : ι → ℝ) (hD0 : ∀ τ, 0 < D τ) (hD : 1 ≤ ∏ τ, D τ)
    {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η) (hη : η ≤ 1)
    (hm : ∀ x ∈ O, ∀ τ i k, ‖m x τ i k‖ ^ 2 ≤ B) (hdet : ∀ x ∈ O, ∀ τ, ‖(m x τ).det‖ = D τ) :
    ∃ N : Finset α, (N : Set α) ⊆ O ∧
      (N.card : ℝ) ≤ (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * Fintype.card ι * r ^ 2) ∧
      ∀ x ∈ O, ∃ y ∈ N, ∀ τ a b,
        ‖(m x τ * (m y τ)⁻¹) a b - (if a = b then 1 else 0)‖ ≤ η := by sorry
