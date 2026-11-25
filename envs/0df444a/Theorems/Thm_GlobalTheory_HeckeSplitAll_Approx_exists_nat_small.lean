-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_exists_nat_small
-- name    : GlobalTheory.HeckeSplitAll.Approx.exists_nat_small
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:34.949354+00:00
-- url     : https://prove2.me/theorems/6944ce70-3d04-576c-8c32-de4fdf397a11
-- title:
--   Approx: exists nat small
-- statement:
--   The Approx construction uses the exists nat small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L69-L77

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

theorem GlobalTheory.HeckeSplitAll.Approx.exists_nat_small (x : F) (hx : x ≠ 0) : ∃ P : ℕ, P ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
    ‖algebraMap F (v.adicCompletion F) x‖ ≠ 1 → ‖(P : v.adicCompletion F)‖ < 1 := by sorry
