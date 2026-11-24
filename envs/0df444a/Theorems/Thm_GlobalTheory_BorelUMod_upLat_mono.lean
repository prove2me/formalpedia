-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_upLat_mono
-- name    : GlobalTheory.BorelUMod.upLat_mono
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:17.488097+00:00
-- url     : https://prove2.me/theorems/bc48b530-012e-4aec-bf1c-8e05297286bb
-- title:
--   Borel UMod: up Lat mono
-- statement:
--   The Borel UMod construction uses the up Lat mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L54-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.BorelUMod.upLat_mono {c C : Fin n → Fin n → ℤ}
    (h : ∀ i j, i < j → c i j ≤ C i j) :
    _root_.GlobalTheory.BorelUMod.upLat L C ≤ _root_.GlobalTheory.BorelUMod.upLat L c := by sorry
