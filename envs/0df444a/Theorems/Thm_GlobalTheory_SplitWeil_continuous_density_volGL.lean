-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_continuous_density_volGL
-- name    : GlobalTheory.SplitWeil.continuous_density_volGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:25.799845+00:00
-- url     : https://prove2.me/theorems/380676ef-672b-43c6-94e6-6dabceba7572
-- title:
--   Split Weil: continuous density vol GL
-- statement:
--   The Split Weil construction uses the continuous density vol GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsMulLeftInvariantVolGL.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsMulLeftInvariantVolGL.lean#L60-L63

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
omit [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitWeil.continuous_density_volGL : Continuous fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) := by sorry
