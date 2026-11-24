-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_map_mul_left_volM
-- name    : GlobalTheory.SplitWeil.map_mul_left_volM
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:16.638804+00:00
-- url     : https://prove2.me/theorems/e1a260f0-e957-4481-9ec5-525b39e6501c
-- title:
--   Split Weil: map mul left vol M
-- statement:
--   The Split Weil construction uses the map mul left vol M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsMulLeftInvariantVolGL.lean#L16-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsMulLeftInvariantVolGL.lean#L16-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.SplitWeil.map_mul_left_volM (h : GL n k) :
    (volM ν n n).map (fun x => h.val * x) =
      ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ))) • volM ν n n := by sorry
