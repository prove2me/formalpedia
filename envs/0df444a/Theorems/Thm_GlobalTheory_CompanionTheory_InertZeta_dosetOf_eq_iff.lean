-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_dosetOf_eq_iff
-- name    : GlobalTheory.CompanionTheory.InertZeta.dosetOf_eq_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:53:57.513858+00:00
-- url     : https://prove2.me/theorems/ef0a0896-7a08-465c-bdf2-ec5ab64000db
-- title:
--   Inert Zeta: doset Of eq iff
-- statement:
--   The Inert Zeta construction uses the doset Of eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean#L46-L54

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

theorem GlobalTheory.CompanionTheory.InertZeta.dosetOf_eq_iff {hK : IsCommensurated K} {x y : G ⧸ K} : dosetOf y = dosetOf x ↔ y ∈ cosetsIn hK x.out := by sorry
