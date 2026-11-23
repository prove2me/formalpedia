-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_mem_skewJ
-- name    : GlobalTheory.BorelUMod.mem_skewJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:42.430721+00:00
-- url     : https://prove2.me/theorems/a387ae4e-84d8-4ae8-bb60-db743c21fabc
-- title:
--   Borel UMod: mem skew J
-- statement:
--   The Borel UMod construction uses the mem skew J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean#L79-L81

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

theorem GlobalTheory.BorelUMod.mem_skewJ {σ : L →+* L} {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.skewJ σ n ↔ _root_.GlobalTheory.BorelUMod.adjJ σ X = -X := by sorry
