-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_finite_fiber
-- name    : GlobalTheory.CompanionTheory.InertZeta.finite_fiber
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:06:06.921446+00:00
-- url     : https://prove2.me/theorems/1cc38e1f-f2de-49cf-b992-1e07d6c6834e
-- title:
--   Inert Zeta: finite fiber
-- statement:
--   The Inert Zeta construction uses the finite fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DoubleCosetSwap.lean#L62-L68

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

theorem GlobalTheory.CompanionTheory.InertZeta.finite_fiber (hK : IsCommensurated K) (q : Set G) : Finite {y : G ⧸ K // dosetOf y = q} := by sorry
