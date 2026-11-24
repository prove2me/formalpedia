-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_exists_int_near
-- name    : GlobalTheory.HeckeSplitAll.Approx.exists_int_near
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:05:20.094308+00:00
-- url     : https://prove2.me/theorems/c2cbf928-4dca-4317-a901-92d6d6359712
-- title:
--   Approx: exists int near
-- statement:
--   The Approx construction uses the exists int near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L79-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L79-L119

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

theorem GlobalTheory.HeckeSplitAll.Approx.exists_int_near (F : Type) [Field F] [NumberField F] : ∃ C : ℝ, 0 < C ∧ ∀ t : InfiniteAdeleRing F,
    ∃ o : 𝓞 F, ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o : F) - t w‖ < C := by sorry
