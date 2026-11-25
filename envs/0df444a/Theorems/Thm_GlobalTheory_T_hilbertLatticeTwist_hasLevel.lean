-- Prove2me | Theorems.Thm_GlobalTheory_T_hilbertLatticeTwist_hasLevel
-- name    : GlobalTheory.T.hilbertLatticeTwist_hasLevel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:31.931105+00:00
-- url     : https://prove2.me/theorems/daff9d02-3d60-588d-8050-80e19cb91cbc
-- title:
--   T: hilbert Lattice Twist has Level
-- statement:
--   The T construction uses the hilbert Lattice Twist has Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertLatticeTwistHasLevelStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertLatticeTwistHasLevelStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistHasLevel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistHasLevelStatement
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

theorem GlobalTheory.T.hilbertLatticeTwist_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)), HasLevel N L → HasLevel N (twist N L α) := by sorry
