-- Prove2me | Theorems.Thm_GlobalTheory_exists_cuspData_rank_one
-- name    : GlobalTheory.exists_cuspData_rank_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:29.503215+00:00
-- url     : https://prove2.me/theorems/1be5ab3c-f1bd-42a6-8e9d-a194e8c1f4f0
-- title:
--   Global Theory: exists cusp Data rank one
-- statement:
--   The Global Theory construction uses the exists cusp Data rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstRaisingMemEquivariant.lean#L403-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstRaisingMemEquivariant.lean#L403-L418

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)
open GlobalTheory

theorem GlobalTheory.exists_cuspData_rank_one : ∃ (X : DataX E4 1) (la : Wt X.Ψ 1) (P : Frame X.Ψ 1 → ℂ) (M : ℝ),
    P ∈ X.SS la ∧ la ≠ 0 ∧ (∃ x ∈ X.dom, P x ≠ 0) ∧ 0 < M ∧ X.Λ = X.L' ∧
    (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E4, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ, (γ : Matrix (Fin 1) (Fin 1) E4).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) := by sorry
