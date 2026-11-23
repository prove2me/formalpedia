-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_cross_term
-- name    : GlobalTheory.Capelli.cross_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:06.092787+00:00
-- url     : https://prove2.me/theorems/248f39c9-b6c3-43a0-802d-d8a382839af1
-- title:
--   Capelli: cross term
-- statement:
--   The Capelli construction uses the cross term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L173-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L173-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]

theorem GlobalTheory.Capelli.cross_term {K σ : Type*} [CommRing K] {p q n : ℕ} (z : Fin p × Fin n → σ)
    (y : Fin q × Fin n → σ) (hzy : ∀ u w, z u ≠ y w) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ a, X (z (a, k)) * pderiv (z (a, l))
        (∑ b, X (y (b, k)) * pderiv (y (b, l)) P)) =
      ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by sorry
