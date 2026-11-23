-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_le_one_iff_int
-- name    : GlobalTheory.HeckeSplitAll.Approx.norm_le_one_iff_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:51.311725+00:00
-- url     : https://prove2.me/theorems/02742235-0e99-4824-a459-400919bd6e40
-- title:
--   Approx: norm le one iff int
-- statement:
--   The Approx construction uses the norm le one iff int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L16-L18

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

theorem GlobalTheory.HeckeSplitAll.Approx.norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by sorry
