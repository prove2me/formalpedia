-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_adjJ_mul
-- name    : GlobalTheory.BorelUMod.adjJ_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:27.972037+00:00
-- url     : https://prove2.me/theorems/6628bc78-40a3-4e0a-9e22-98cc494bf349
-- title:
--   Borel UMod: adj J mul
-- statement:
--   The Borel UMod construction uses the adj J mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L85-L91

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

theorem GlobalTheory.BorelUMod.adjJ_mul (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X * Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ Y * _root_.GlobalTheory.BorelUMod.adjJ σ X := by sorry
