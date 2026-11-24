-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Swap_ex_high
-- name    : GlobalTheory.SatakeWeyl.Swap.ex_high
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:28:18.912188+00:00
-- url     : https://prove2.me/theorems/c7f76f9e-f3c0-4a00-8e5b-5ac59079117a
-- title:
--   Swap: ex high
-- statement:
--   The Swap construction uses the ex high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffAdjacentSwapOfLeviReduction.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffAdjacentSwapOfLeviReduction.lean#L27-L32

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReduction
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
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Swap

theorem GlobalTheory.SatakeWeyl.Swap.ex_high {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (c : Fin n) (k : Fin m) (h : c.val + k.val + 1 = n) :
    ex n m a c = -a k := by sorry
