-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_PrimeRead_aeval_int_eq
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.aeval_int_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:34.00602+00:00
-- url     : https://prove2.me/theorems/5adcc1f2-c144-49dc-bb72-1fb2905258ef
-- title:
--   Prime Read: aeval int eq
-- statement:
--   The Prime Read construction uses the aeval int eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L23-L35

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_BoundaryOnPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.aeval_int_eq {σ Ω : Type} [CommRing Ω] [Algebra ℚ Ω] (τ : σ → Ω)
    (g : MvPolynomial σ ℤ) : aeval τ g = aeval τ (map (Int.castRingHom ℚ) g) := by sorry
