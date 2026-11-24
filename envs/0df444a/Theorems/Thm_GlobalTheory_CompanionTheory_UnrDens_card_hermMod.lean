-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_hermMod
-- name    : GlobalTheory.CompanionTheory.UnrDens.card_hermMod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:32.99638+00:00
-- url     : https://prove2.me/theorems/93ebb47e-3d9d-4c0f-b1c4-8b35717263d1
-- title:
--   Unr Dens: card herm Mod
-- statement:
--   The Unr Dens construction uses the card herm Mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianMatricesModPow.lean#L54-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianMatricesModPow.lean#L54-L91

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianMatricesModPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens

theorem GlobalTheory.CompanionTheory.UnrDens.card_hermMod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by sorry
