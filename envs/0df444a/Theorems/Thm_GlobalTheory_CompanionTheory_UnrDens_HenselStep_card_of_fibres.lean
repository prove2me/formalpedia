-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_card_of_fibres
-- name    : GlobalTheory.CompanionTheory.UnrDens.HenselStep.card_of_fibres
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:40.280849+00:00
-- url     : https://prove2.me/theorems/91ede2d5-e50f-469a-92a2-b122be23ed06
-- title:
--   Hensel Step: card of fibres
-- statement:
--   The Hensel Step construction uses the card of fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean#L13-L18

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep

theorem GlobalTheory.CompanionTheory.UnrDens.HenselStep.card_of_fibres {α β : Type*} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (h : ∀ b, Nat.card {a // f a = b} = c) : Nat.card α = Nat.card β * c := by sorry
