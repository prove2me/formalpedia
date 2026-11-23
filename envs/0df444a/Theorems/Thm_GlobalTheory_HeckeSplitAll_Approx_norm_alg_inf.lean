-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_alg_inf
-- name    : GlobalTheory.HeckeSplitAll.Approx.norm_alg_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:20.162402+00:00
-- url     : https://prove2.me/theorems/8747a7a1-659e-4fd0-ae89-23bc9dcab112
-- title:
--   Approx: norm alg inf
-- statement:
--   The Approx construction uses the norm alg inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFinsetNormOne.lean#L12-L14

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

theorem GlobalTheory.HeckeSplitAll.Approx.norm_alg_inf (w : InfinitePlace F) (x : F) : ‖algebraMap F w.Completion x‖ = w x := by sorry
