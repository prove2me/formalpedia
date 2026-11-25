-- Prove2me | Theorems.Thm_GlobalTheory_RegulatorClassBound_exists_mem_box
-- name    : GlobalTheory.RegulatorClassBound.exists_mem_box
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:15:07.321697+00:00
-- url     : https://prove2.me/theorems/e10355c7-e8da-5aa2-9b6a-7eb20b917baf
-- title:
--   Regulator Class Bound: exists mem box
-- statement:
--   The Regulator Class Bound construction uses the exists mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RegulatorLeSumSmallIdealsInClass.lean#L14-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RegulatorLeSumSmallIdealsInClass.lean#L14-L67

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

theorem GlobalTheory.RegulatorClassBound.exists_mem_box (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (c : InfinitePlace K → ℝ)
    (hc : ∑ w, (w.mult : ℝ) * c w = Real.log ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|)) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ w : InfinitePlace K, w (a : K) < Real.exp (c w) := by sorry
