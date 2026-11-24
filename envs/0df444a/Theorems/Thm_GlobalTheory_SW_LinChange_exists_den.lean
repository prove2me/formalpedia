-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_exists_den
-- name    : GlobalTheory.SW.LinChange.exists_den
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:42.543949+00:00
-- url     : https://prove2.me/theorems/c23fddd8-e372-4068-b0e0-0acfa458d1ab
-- title:
--   Lin Change: exists den
-- statement:
--   The Lin Change construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L90-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L90-L110

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

theorem GlobalTheory.SW.LinChange.exists_den (T : Matrix κ ι K →ₗ[ℚ] Matrix κ ι K) :
    ∃ M : ℕ, 0 < M ∧ ∀ y, IntM y → IntM ((M : K) • T y) := by sorry
