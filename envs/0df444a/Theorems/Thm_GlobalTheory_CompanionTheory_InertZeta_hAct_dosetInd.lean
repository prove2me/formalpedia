-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_hAct_dosetInd
-- name    : GlobalTheory.CompanionTheory.InertZeta.hAct_dosetInd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:51.447683+00:00
-- url     : https://prove2.me/theorems/14821860-0646-4f26-ac0f-842dc0f8bbaf
-- title:
--   Inert Zeta: h Act doset Ind
-- statement:
--   The Inert Zeta construction uses the h Act doset Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean#L24-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DoubleCosetSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {G : Type} [Group G] {K : Subgroup G}

theorem GlobalTheory.CompanionTheory.InertZeta.hAct_dosetInd (hK : IsCommensurated K) (g : G) (f : G → ℂ) :
    hAct K (dosetInd ℂ K g) f 1 = ∑ x ∈ cosetsIn hK g, f x.out := by sorry
