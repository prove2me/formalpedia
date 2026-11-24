-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Four_unitaryFourUpperLeftBlock_mul_of_mem_levi
-- name    : GlobalTheory.SatakeWeyl.Four.unitaryFourUpperLeftBlock_mul_of_mem_levi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:27.980892+00:00
-- url     : https://prove2.me/theorems/4f62380b-7ea4-4fe2-be58-49e3abdb6f65
-- title:
--   Four: unitary Four Upper Left Block mul of mem levi
-- statement:
--   The Four construction uses the unitary Four Upper Left Block mul of mem levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2CartanDoubleCosets.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2CartanDoubleCosets.lean#L15-L23

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosets
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
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Four
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem GlobalTheory.SatakeWeyl.Four.unitaryFourUpperLeftBlock_mul_of_mem_levi {g : GU σ 4} (g' : GU σ 4) (hg : g ∈ leviU σ ![0, 0, 1, 1]) :
    unitaryFourUpperLeftBlock (g * g') = unitaryFourUpperLeftBlock g * unitaryFourUpperLeftBlock g' := by sorry
