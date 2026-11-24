-- Prove2me | Theorems.Thm_GlobalTheory_CondRescale_norm_le_one_of_pow_near
-- name    : GlobalTheory.CondRescale.norm_le_one_of_pow_near
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:48.33014+00:00
-- url     : https://prove2.me/theorems/ced64558-be7c-48da-a78b-f7b0146c81fc
-- title:
--   Cond Rescale: norm le one of pow near
-- statement:
--   The Cond Rescale construction uses the norm le one of pow near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalCharacterConductorExists.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalCharacterConductorExists.lean#L12-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalCharacterConductorExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open scoped Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CondRescale
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CondRescale.norm_le_one_of_pow_near (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1) : ‖z‖ ≤ 1 := by sorry
