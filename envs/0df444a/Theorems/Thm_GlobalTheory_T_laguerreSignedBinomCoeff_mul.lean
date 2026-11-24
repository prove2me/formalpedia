-- Prove2me | Theorems.Thm_GlobalTheory_T_laguerreSignedBinomCoeff_mul
-- name    : GlobalTheory.T.laguerreSignedBinomCoeff_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:51:07.501305+00:00
-- url     : https://prove2.me/theorems/17c5ce85-b340-4b66-b220-2204a1324fa1
-- title:
--   T: laguerre Signed Binom Coeff mul
-- statement:
--   The T construction uses the laguerre Signed Binom Coeff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaguerreSignedBinomCoeffMulStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaguerreSignedBinomCoeffMulStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaguerreSignedBinomCoeffMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaguerreSignedBinomCoeffMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.laguerreSignedBinomCoeff_mul : ∀ k n m j : ℕ, j ≤ m → m ≤ n → rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by sorry
