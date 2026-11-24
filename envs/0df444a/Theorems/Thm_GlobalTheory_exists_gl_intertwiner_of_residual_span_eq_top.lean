-- Prove2me | Theorems.Thm_GlobalTheory_exists_gl_intertwiner_of_residual_span_eq_top
-- name    : GlobalTheory.exists_gl_intertwiner_of_residual_span_eq_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:15.705278+00:00
-- url     : https://prove2.me/theorems/b45760ee-ac3f-4b49-bbb6-70ac808c9ea2
-- title:
--   Global Theory: exists gl intertwiner of residual span eq top
-- statement:
--   The Global Theory construction uses the exists gl intertwiner of residual span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlIntertwinerOfResidualSpanEqTop.lean#L48-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlIntertwinerOfResidualSpanEqTop.lean#L48-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlIntertwinerOfResidualSpanEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.exists_gl_intertwiner_of_residual_span_eq_top :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type) [Group G] (r : ℕ) (ρ ρ' : G →* Matrix.GeneralLinearGroup (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∃ A : Matrix (Fin r) (Fin r) O, A.det ≠ 0 ∧ ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * A = A * ρ g) → ∃ U : Matrix.GeneralLinearGroup (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by sorry
