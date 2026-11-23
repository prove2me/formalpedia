-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_adjJ_smul
-- name    : GlobalTheory.BorelUMod.adjJ_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:46:12.979846+00:00
-- url     : https://prove2.me/theorems/69ad43ae-1057-4e13-8ec4-83bf09582bf3
-- title:
--   Borel UMod: adj J smul
-- statement:
--   The Borel UMod construction uses the adj J smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L111-L114

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
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.BorelUMod.adjJ_smul (σ : L →+* L) (a : L) (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (a • X) = σ a • _root_.GlobalTheory.BorelUMod.adjJ σ X := by sorry
