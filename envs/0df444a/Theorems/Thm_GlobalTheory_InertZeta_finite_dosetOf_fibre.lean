-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_finite_dosetOf_fibre
-- name    : GlobalTheory.InertZeta.finite_dosetOf_fibre
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:48:34.431108+00:00
-- url     : https://prove2.me/theorems/eb4f78cb-9548-40dd-aa3b-0691f4ac8f79
-- title:
--   Inert Zeta: finite doset Of fibre
-- statement:
--   The Inert Zeta construction uses the finite doset Of fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BiInvariantReplaceSameDoubleCosetSums.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BiInvariantReplaceSameDoubleCosetSums.lean#L33-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open GlobalTheory GlobalTheory.InertZeta
open Formalism.UG
variable {G : Type} [Group G] {K : Subgroup G}

theorem GlobalTheory.InertZeta.finite_dosetOf_fibre (hK : IsCommensurated K) (S : Set G) :
    Finite {x : G ⧸ K // dosetOf K x = S} := by sorry
