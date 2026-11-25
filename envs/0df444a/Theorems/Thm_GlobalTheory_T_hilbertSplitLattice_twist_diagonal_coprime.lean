-- Prove2me | Theorems.Thm_GlobalTheory_T_hilbertSplitLattice_twist_diagonal_coprime
-- name    : GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:51.588059+00:00
-- url     : https://prove2.me/theorems/5423d1d1-b6b9-5536-8d44-88588d13535e
-- title:
--   T: hilbert Split Lattice twist diagonal coprime
-- statement:
--   The T construction uses the hilbert Split Lattice twist diagonal coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertSplitLatticeTwistDiagonalCoprimeStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertSplitLatticeTwistDiagonalCoprimeStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertSplitLatticeTwistDiagonalCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertSplitLatticeTwistDiagonalCoprimeStatement
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

theorem GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by sorry
