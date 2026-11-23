-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_mem_upLat
-- name    : GlobalTheory.BorelUMod.mem_upLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:46:20.693476+00:00
-- url     : https://prove2.me/theorems/e30cd994-e126-45b7-9fc3-ce2dd900c476
-- title:
--   Borel UMod: mem up Lat
-- statement:
--   The Borel UMod construction uses the mem up Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L21-L25

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

theorem GlobalTheory.BorelUMod.mem_upLat {c : Fin n → Fin n → ℤ}
    {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.upLat L c ↔
      (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j) := by sorry
