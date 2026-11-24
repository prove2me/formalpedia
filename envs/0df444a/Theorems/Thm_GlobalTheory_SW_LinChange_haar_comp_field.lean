-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_haar_comp_field
-- name    : GlobalTheory.SW.LinChange.haar_comp_field
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:37.249027+00:00
-- url     : https://prove2.me/theorems/e289b211-d80d-4df4-ac52-a51d194212fa
-- title:
--   Lin Change: haar comp field
-- statement:
--   The Lin Change construction uses the haar comp field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L236-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L236-L242

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

theorem GlobalTheory.SW.LinChange.haar_comp_field (f : Matrix κ ι K →ₗ[K] Matrix κ ι K) (hf : LinearMap.det f ≠ 0)
    (φ : Matrix κ ι K → ℂ) (hφ : IsSB φ) :
    IsSB (fun x => φ (f x)) ∧
      haar (fun x => φ (f x)) = ((|Algebra.norm ℚ (LinearMap.det f)| : ℚ) : ℂ) * haar φ := by sorry
