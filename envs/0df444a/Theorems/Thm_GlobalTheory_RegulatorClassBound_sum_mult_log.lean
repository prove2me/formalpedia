-- Prove2me | Theorems.Thm_GlobalTheory_RegulatorClassBound_sum_mult_log
-- name    : GlobalTheory.RegulatorClassBound.sum_mult_log
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:15:10.576803+00:00
-- url     : https://prove2.me/theorems/9d59e71d-8962-489f-8ce6-26a737d954d9
-- title:
--   Regulator Class Bound: sum mult log
-- statement:
--   The Regulator Class Bound construction uses the sum mult log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RegulatorLeSumSmallIdealsInClass.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RegulatorLeSumSmallIdealsInClass.lean#L69-L78

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CovolumeLeSumVolumeOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_VolumePosSimplexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Finset
open GlobalTheory GlobalTheory.RegulatorClassBound
open NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem Module
open scoped nonZeroDivisors

theorem GlobalTheory.RegulatorClassBound.sum_mult_log (K : Type) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (a : K)) =
      Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) := by sorry
