-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_int_le_one
-- name    : GlobalTheory.HeckeSplitAll.Approx.norm_int_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:47.376677+00:00
-- url     : https://prove2.me/theorems/d31b9836-14a4-405c-acd5-df424b8dab3d
-- title:
--   Approx: norm int le one
-- statement:
--   The Approx construction uses the norm int le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L23-L25

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

theorem GlobalTheory.HeckeSplitAll.Approx.norm_int_le_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ ≤ 1 := by sorry
