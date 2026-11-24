-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_continuous_adjJ
-- name    : GlobalTheory.BorelUMod.continuous_adjJ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:02:50.857812+00:00
-- url     : https://prove2.me/theorems/bbac3452-765e-4023-9bad-53b27c42b00a
-- title:
--   Borel UMod: continuous adj J
-- statement:
--   The Borel UMod construction uses the continuous adj J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnipLatIsOpenIsCompact.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnipLatIsOpenIsCompact.lean#L49-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.BorelUMod.continuous_adjJ {σ : L →+* L} (hσ : Continuous σ) (n : ℕ) :
    Continuous (adjJ σ : Matrix (Fin n) (Fin n) L → Matrix (Fin n) (Fin n) L) := by sorry
