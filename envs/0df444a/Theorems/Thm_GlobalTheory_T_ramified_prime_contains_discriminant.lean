-- Prove2me | Theorems.Thm_GlobalTheory_T_ramified_prime_contains_discriminant
-- name    : GlobalTheory.T.ramified_prime_contains_discriminant
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:56:19.410934+00:00
-- url     : https://prove2.me/theorems/3068ab7e-7cbd-47ad-9019-276c58745dc7
-- title:
--   T: ramified prime contains discriminant
-- statement:
--   The T construction uses the ramified prime contains discriminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RamifiedPrimeContainsDiscriminantStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RamifiedPrimeContainsDiscriminantStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RamifiedPrimeContainsDiscriminant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RamifiedPrimeContainsDiscriminantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ramified_prime_contains_discriminant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by sorry
