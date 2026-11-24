-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_haar_comp
-- name    : GlobalTheory.SW.LinChange.haar_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:38.407641+00:00
-- url     : https://prove2.me/theorems/5d1ffbb2-f55e-4324-9cf4-53ea0421ad07
-- title:
--   Lin Change: haar comp
-- statement:
--   The Lin Change construction uses the haar comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L210-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L210-L234

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

theorem GlobalTheory.SW.LinChange.haar_comp (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (φ : Matrix κ ι K → ℂ) (hφ : IsSB φ) :
    IsSB (fun x => φ (T x)) ∧
      haar (fun x => φ (T x)) = ((|LinearMap.det T.toLinearMap| : ℚ) : ℂ) * haar φ := by sorry
