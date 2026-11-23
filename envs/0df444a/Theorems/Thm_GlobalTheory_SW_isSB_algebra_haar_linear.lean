-- Prove2me | Theorems.Thm_GlobalTheory_SW_isSB_algebra_haar_linear
-- name    : GlobalTheory.SW.isSB_algebra_haar_linear
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:39.88332+00:00
-- url     : https://prove2.me/theorems/12231e68-d883-4b72-a1be-d3ef20218d83
-- title:
--   SW: is SB algebra haar linear
-- statement:
--   The SW construction uses the is SB algebra haar linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L97-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L97-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
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
open GlobalTheory.SW.HaarAlg

theorem GlobalTheory.SW.isSB_algebra_haar_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by sorry
