-- Prove2me | Theorems.Thm_GlobalTheory_CharIdem_sum_fiber_nonneg
-- name    : GlobalTheory.CharIdem.sum_fiber_nonneg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:30:04.112859+00:00
-- url     : https://prove2.me/theorems/87cca30b-a628-42ef-bd02-c7cdb919b089
-- title:
--   Char Idem: sum fiber nonneg
-- statement:
--   The Char Idem construction uses the sum fiber nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CharFnLocallyConstant.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CharFnLocallyConstant.lean#L20-L43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CharFnLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.CharIdem
variable {G : Type} [Group G]
variable (K : Subgroup G) (χ : K →* Circle) (c : ℝ)

theorem GlobalTheory.CharIdem.sum_fiber_nonneg {ι Q : Type} [Fintype ι] [DecidableEq Q] (q : ι → Q) (a : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, (if q i = q j then star (a i) * a j else 0) := by sorry
