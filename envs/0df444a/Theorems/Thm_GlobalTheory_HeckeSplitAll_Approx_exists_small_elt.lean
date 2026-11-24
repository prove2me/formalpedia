-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_exists_small_elt
-- name    : GlobalTheory.HeckeSplitAll.Approx.exists_small_elt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:10.614352+00:00
-- url     : https://prove2.me/theorems/2fc991bb-5b9b-4501-84d7-de42362e2d72
-- title:
--   Approx: exists small elt
-- statement:
--   The Approx construction uses the exists small elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L124-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L124-L170

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology Filter
open GlobalTheory GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
variable {F : Type} [Field F] [NumberField F]
open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module
open scoped nonZeroDivisors

theorem GlobalTheory.HeckeSplitAll.Approx.exists_small_elt (v₀ : HeightOneSpectrum (𝓞 F)) (η : ℝ) (hη : 0 < η) :
    ∃ x : F, x ≠ 0 ∧ (∀ w : InfinitePlace F, w x < η) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := by sorry
