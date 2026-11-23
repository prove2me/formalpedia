-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_map_nat_smul
-- name    : GlobalTheory.SW.LinChange.map_nat_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:10.409699+00:00
-- url     : https://prove2.me/theorems/700d0a9d-f7c7-4f3f-ab14-3b448e3f7ec8
-- title:
--   Lin Change: map nat smul
-- statement:
--   The Lin Change construction uses the map nat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L112-L114

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

theorem GlobalTheory.SW.LinChange.map_nat_smul (T : Matrix κ ι K →ₗ[ℚ] Matrix κ ι K) (M : ℕ) (y : Matrix κ ι K) :
    T ((M : K) • y) = (M : K) • T y := by sorry
