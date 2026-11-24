-- Prove2me | Theorems.Thm_GlobalTheory_T_card_residueField_adjoin_unitary_prod
-- name    : GlobalTheory.T.card_residueField_adjoin_unitary_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:27:43.300697+00:00
-- url     : https://prove2.me/theorems/832d9496-a98a-47df-94fe-5b09544bcf4b
-- title:
--   T: card residue Field adjoin unitary prod
-- statement:
--   The T construction uses the card residue Field adjoin unitary prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardResidueFieldAdjoinUnitaryProdStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardResidueFieldAdjoinUnitaryProdStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_residueField_adjoin_unitary_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by sorry
