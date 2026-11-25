-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_strong_approx
-- name    : GlobalTheory.HeckeSplitAll.Approx.strong_approx
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:35.92681+00:00
-- url     : https://prove2.me/theorems/0d8b647e-0daf-4159-a077-f3aebedbf2b2
-- title:
--   Approx: strong approx
-- statement:
--   The Approx construction uses the strong approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L172-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L172-L223

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

theorem GlobalTheory.HeckeSplitAll.Approx.strong_approx (v₀ : HeightOneSpectrum (𝓞 F)) (t : InfiniteAdeleRing F) (s : FiniteAdeleRing (𝓞 F) F)
    (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : F, c ≠ 0 ∧ (∀ w : InfinitePlace F, ‖algebraMap F w.Completion c - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) c - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by sorry
