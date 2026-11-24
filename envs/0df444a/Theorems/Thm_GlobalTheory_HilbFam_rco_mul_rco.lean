-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_rco_mul_rco
-- name    : GlobalTheory.HilbFam.rco_mul_rco
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:22:03.119816+00:00
-- url     : https://prove2.me/theorems/10afe7f3-fc1e-4230-85c8-03fc68dcc103
-- title:
--   Hilb Fam: rco mul rco
-- statement:
--   The Hilb Fam construction uses the rco mul rco property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaguerreSignedBinomCoeffMul.lean#L11-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaguerreSignedBinomCoeffMul.lean#L11-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaguerreSignedBinomCoeffMul
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
open GlobalTheory GlobalTheory.HilbFam

theorem GlobalTheory.HilbFam.rco_mul_rco : ∀ k n m j : ℕ, j ≤ m → m ≤ n →
    rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by sorry
