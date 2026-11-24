-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_exists_eq_split_of_hasLevel
-- name    : GlobalTheory.HilbFam.exists_eq_split_of_hasLevel
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:20:32.810505+00:00
-- url     : https://prove2.me/theorems/f0bbb73e-98f7-44aa-ae81-87f6752be8b4
-- title:
--   Hilb Fam: exists eq split of has Level
-- statement:
--   The Hilb Fam construction uses the exists eq split of has Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSplitOfHilbertLatticeHasLevel.lean#L23-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSplitOfHilbertLatticeHasLevel.lean#L23-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
variable {F : Type} [Field F] [NumberField F]
set_option autoImplicit false
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HilbFam.exists_eq_split_of_hasLevel (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (hN : 0 < N) (hL : _root_.GlobalTheory.HilbFam.HasLevel N L) :
    ∃ (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (x : F), L = _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x := by sorry
