-- Prove2me | Theorems.Thm_GlobalTheory_T_hilbertEisensteinLatticeJet_split_direction_add
-- name    : GlobalTheory.T.hilbertEisensteinLatticeJet_split_direction_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:02.177402+00:00
-- url     : https://prove2.me/theorems/52b42729-bb4f-4138-a4cc-d56445ec14b6
-- title:
--   T: hilbert Eisenstein Lattice Jet split direction add
-- statement:
--   The T construction uses the hilbert Eisenstein Lattice Jet split direction add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeJetSplitDirectionAddStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeJetSplitDirectionAddStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSplitDirectionAdd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSplitDirectionAddStatement
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

theorem GlobalTheory.T.hilbertEisensteinLatticeJet_split_direction_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet k (split 𝔞 𝔟 x) μ τ c t := by sorry
