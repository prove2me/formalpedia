-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_map_perSub_le
-- name    : GlobalTheory.SW.LinChange.map_perSub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:07.033114+00:00
-- url     : https://prove2.me/theorems/49a8e985-2dee-4d33-95aa-0b3cdff42d43
-- title:
--   Lin Change: map per Sub le
-- statement:
--   The Lin Change construction uses the map per Sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L116-L123

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

theorem GlobalTheory.SW.LinChange.map_perSub_le (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (R M : ℕ)
    (hT : ∀ y, IntM y → IntM ((M : K) • T y)) :
    (perSub K κ ι (R * M)).map T.toAddEquiv.toAddMonoidHom ≤ perSub K κ ι R := by sorry
