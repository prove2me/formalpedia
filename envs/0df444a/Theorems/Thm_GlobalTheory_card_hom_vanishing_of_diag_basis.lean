-- Prove2me | Theorems.Thm_GlobalTheory_card_hom_vanishing_of_diag_basis
-- name    : GlobalTheory.card_hom_vanishing_of_diag_basis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:58.700394+00:00
-- url     : https://prove2.me/theorems/c878decd-297d-4be8-a00d-940b9e95d8d1
-- title:
--   Global Theory: card hom vanishing of diag basis
-- statement:
--   The Global Theory construction uses the card hom vanishing of diag basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CardHomVanishingOfDiagBasis.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CardHomVanishingOfDiagBasis.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.card_hom_vanishing_of_diag_basis {M A ι : Type} [AddCommGroup M] [AddCommGroup A]
    [Fintype ι] (N : Submodule ℤ M) (b : Basis ι ℤ M) (c : Basis ι ℤ N) (a : ι → ℤ)
    (h : ∀ i, (c i : M) = a i • b i) :
    Nat.card {f : M →ₗ[ℤ] A // ∀ x ∈ N, f x = 0} = ∏ i, Nat.card {y : A // a i • y = 0} := by sorry
