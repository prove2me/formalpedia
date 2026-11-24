-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_hermitian_resAlg
-- name    : GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:44.364857+00:00
-- url     : https://prove2.me/theorems/58ec3391-3985-4c62-88f4-d14157ae9e3a
-- title:
--   Unr Dens: card hermitian res Alg
-- statement:
--   The Unr Dens construction uses the card hermitian res Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatricesCard.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatricesCard.lean#L9-L40

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatricesCard
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

theorem GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (n : ℕ) :
    Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by sorry
