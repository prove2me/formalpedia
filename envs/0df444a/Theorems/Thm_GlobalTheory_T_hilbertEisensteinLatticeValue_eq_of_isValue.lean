-- Prove2me | Theorems.Thm_GlobalTheory_T_hilbertEisensteinLatticeValue_eq_of_isValue
-- name    : GlobalTheory.T.hilbertEisensteinLatticeValue_eq_of_isValue
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:11.50444+00:00
-- url     : https://prove2.me/theorems/4fca9565-2cd7-50b8-afdb-1237eafef5dd
-- title:
--   T: hilbert Eisenstein Lattice Value eq of is Value
-- statement:
--   The T construction uses the hilbert Eisenstein Lattice Value eq of is Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeValueEqOfIsValueStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeValueEqOfIsValueStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeValueEqOfIsValue
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeValueEqOfIsValueStatement
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

theorem GlobalTheory.T.hilbertEisensteinLatticeValue_eq_of_isValue : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : Lat F) (b a : Emb F → ℂ) (G : ℂ), IsGVal k L b a G → gval k L b a = G := by sorry
