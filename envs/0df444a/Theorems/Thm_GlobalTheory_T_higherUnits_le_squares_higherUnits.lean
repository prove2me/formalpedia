-- Prove2me | Theorems.Thm_GlobalTheory_T_higherUnits_le_squares_higherUnits
-- name    : GlobalTheory.T.higherUnits_le_squares_higherUnits
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:48.807746+00:00
-- url     : https://prove2.me/theorems/c36bea0b-7d36-4414-9625-c04027a36850
-- title:
--   T: higher Units le squares higher Units
-- statement:
--   The T construction uses the higher Units le squares higher Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HigherUnitsLeSquaresHigherUnitsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HigherUnitsLeSquaresHigherUnitsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnitsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.higherUnits_le_squares_higherUnits : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) → hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤ sqs (hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by sorry
