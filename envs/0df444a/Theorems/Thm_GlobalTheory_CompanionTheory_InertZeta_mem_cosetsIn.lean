-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_mem_cosetsIn
-- name    : GlobalTheory.CompanionTheory.InertZeta.mem_cosetsIn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:53:23.913639+00:00
-- url     : https://prove2.me/theorems/59f6449e-77ab-41c8-97f1-ad9b6678f71a
-- title:
--   Inert Zeta: mem cosets In
-- statement:
--   The Inert Zeta construction uses the mem cosets In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean#L15-L22

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

theorem GlobalTheory.CompanionTheory.InertZeta.mem_cosetsIn {hK : IsCommensurated K} {g : G} {x : G ⧸ K} :
    x ∈ cosetsIn hK g ↔ x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by sorry
