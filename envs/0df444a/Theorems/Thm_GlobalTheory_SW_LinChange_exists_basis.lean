-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_exists_basis
-- name    : GlobalTheory.SW.LinChange.exists_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:30.194796+00:00
-- url     : https://prove2.me/theorems/48bf612d-88bc-4094-b253-8507f344b632
-- title:
--   Lin Change: exists basis
-- statement:
--   The Lin Change construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L71-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L71-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.LinChange.exists_basis : ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
    (b : Module.Basis J ℚ (Matrix κ ι K)),
    ∀ x, x ∈ AddSubgroup.closure (Set.range b) ↔ IntM x := by sorry
