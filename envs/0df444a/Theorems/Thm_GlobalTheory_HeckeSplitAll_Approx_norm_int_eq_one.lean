-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_int_eq_one
-- name    : GlobalTheory.HeckeSplitAll.Approx.norm_int_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:42.498927+00:00
-- url     : https://prove2.me/theorems/33d18921-b909-4f10-b190-1154e12e5d0a
-- title:
--   Approx: norm int eq one
-- statement:
--   The Approx construction uses the norm int eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L27-L34

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

theorem GlobalTheory.HeckeSplitAll.Approx.norm_int_eq_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) (ho : o ∉ v.asIdeal) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ = 1 := by sorry
