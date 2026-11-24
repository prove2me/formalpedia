-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_quot_lev
-- name    : GlobalTheory.CompanionTheory.UnrDens.card_quot_lev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:54.023339+00:00
-- url     : https://prove2.me/theorems/75636c09-aa0e-4d01-ab10-7d68b10479d3
-- title:
--   Unr Dens: card quot lev
-- statement:
--   The Unr Dens construction uses the card quot lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuotientCard.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuotientCard.lean#L69-L82

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens

theorem GlobalTheory.CompanionTheory.UnrDens.card_quot_lev : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by sorry
