-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_mem_dosetOf_iff
-- name    : GlobalTheory.InertZeta.mem_dosetOf_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:48:47.920794+00:00
-- url     : https://prove2.me/theorems/78343683-26e0-46ff-b9f0-347d5ad6355f
-- title:
--   Inert Zeta: mem doset Of iff
-- statement:
--   The Inert Zeta construction uses the mem doset Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BiInvariantReplaceSameDoubleCosetSums.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BiInvariantReplaceSameDoubleCosetSums.lean#L18-L26

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

theorem GlobalTheory.InertZeta.mem_dosetOf_iff {x y : G ⧸ K} :
    y.out ∈ DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G) ↔ dosetOf K y = dosetOf K x := by sorry
