-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_mem_K_iff
-- name    : GlobalTheory.SatakeWeyl.IdxFour.mem_K_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:34.470215+00:00
-- url     : https://prove2.me/theorems/c9e2a1e7-9948-4711-9b0f-690b4bfe6a8e
-- title:
--   Idx Four: mem K iff
-- statement:
--   The Idx Four construction uses the mem K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2RootIndexOfCardSq.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2RootIndexOfCardSq.lean#L74-L82

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.IdxFour
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem GlobalTheory.SatakeWeyl.IdxFour.mem_K_iff (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) :
    g ∈ KU σ 4 ↔ x ∈ intL L := by sorry
