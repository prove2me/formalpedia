-- Prove2me | Theorems.Thm_GlobalTheory_RegulatorClassBound_regulator_le_sum_class
-- name    : GlobalTheory.RegulatorClassBound.regulator_le_sum_class
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:02.617694+00:00
-- url     : https://prove2.me/theorems/654bede8-5139-4328-88c4-de5cfadde866
-- title:
--   Regulator Class Bound: regulator le sum class
-- statement:
--   The Regulator Class Bound construction uses the regulator le sum class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RegulatorLeSumSmallIdealsInClass.lean#L80-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RegulatorLeSumSmallIdealsInClass.lean#L80-L189

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

theorem GlobalTheory.RegulatorClassBound.regulator_le_sum_class : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ (C : ClassGroup (𝓞 K)) (S : Finset (Ideal (𝓞 K))), (∀ I, I ∈ S ↔ ∃ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)), ClassGroup.mk0 ⟨I, hI⟩ = C ∧ (Ideal.absNorm I : ℝ) ≤ Real.sqrt |(discr K : ℝ)|) → Units.regulator K ≤ ∑ I ∈ S, Real.log (Real.sqrt |(discr K : ℝ)| / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) := by sorry
