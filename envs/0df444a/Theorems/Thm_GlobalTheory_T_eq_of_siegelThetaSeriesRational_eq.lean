-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_of_siegelThetaSeriesRational_eq
-- name    : GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:32:47.749243+00:00
-- url     : https://prove2.me/theorems/dc963074-f13c-4218-9d7a-5a21af1d7956
-- title:
--   T: eq of siegel Theta Series Rational eq
-- statement:
--   The T construction uses the eq of siegel Theta Series Rational eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EqOfSiegelThetaSeriesRationalEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EqOfSiegelThetaSeriesRationalEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEqStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by sorry
