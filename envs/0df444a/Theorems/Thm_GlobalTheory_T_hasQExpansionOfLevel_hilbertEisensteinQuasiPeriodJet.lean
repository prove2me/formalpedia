-- Prove2me | Theorems.Thm_GlobalTheory_T_hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet
-- name    : GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:33.452608+00:00
-- url     : https://prove2.me/theorems/97a6440a-905b-55dd-bc8e-2f0aa6701ce4
-- title:
--   T: has QExpansion Of Level hilbert Eisenstein Quasi Period Jet
-- statement:
--   The T construction uses the has QExpansion Of Level hilbert Eisenstein Quasi Period Jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelHilbertEisensteinQuasiPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement
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

theorem GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (N : ℕ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ) (c : ℕ → ℂ), 0 < N → Even k → IsCoef k 𝔞 𝔟 a₀ a → HasLevel N (split 𝔞 𝔟 x) → HasQ N Ch c → HasQ N (hfun k (split 𝔞 𝔟 x) κ Ch) (fun n ↦ PowerSeries.coeff n (hser k N 𝔞 a x κ c)) := by sorry
