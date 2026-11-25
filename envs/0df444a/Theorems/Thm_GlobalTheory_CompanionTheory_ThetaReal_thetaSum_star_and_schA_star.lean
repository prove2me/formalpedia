-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaReal_thetaSum_star_and_schA_star
-- name    : GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:58.154802+00:00
-- url     : https://prove2.me/theorems/bc6c7d55-bc9d-47f2-a8fc-663887c472da
-- title:
--   Theta Real: theta Sum star and sch A star
-- statement:
--   The Theta Real construction uses the theta Sum star and sch A star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ThetaSumStarAndSchAStar.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ThetaSumStarAndSchAStar.lean#L9-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ThetaSumStarAndSchAStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaReal

theorem GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    thetaSum F (star Φ) = conj (thetaSum F Φ) ∧ (Φ ∈ schA F κ → star Φ ∈ schA F κ) := by sorry
