-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_mem_root_iff
-- name    : GlobalTheory.SatakeWeyl.Heis.mem_root_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:15.756245+00:00
-- url     : https://prove2.me/theorems/fa820bc8-f197-4db9-ad70-2efcc922dbca
-- title:
--   Heis: mem root iff
-- statement:
--   The Heis construction uses the mem root iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L33-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L33-L64

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
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
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem GlobalTheory.SatakeWeyl.Heis.mem_root_iff (hσ : ∀ x, σ (σ x) = x) (g : GU σ 3) :
    g ∈ rootU σ ![0, 0, 0] ↔ ∃ x y, y + σ y + x * σ x = 0 ∧ mat g = Heisenberg₂ σ x y := by sorry
