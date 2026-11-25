-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_PrimeRead_aeval_eq_image
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.aeval_eq_image
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:06.752637+00:00
-- url     : https://prove2.me/theorems/378f7247-aeeb-4ee2-8c86-12ed0d10726f
-- title:
--   Prime Read: aeval eq image
-- statement:
--   The Prime Read construction uses the aeval eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L9-L21

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.aeval_eq_image {σ E : Type} [CommRing E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (G : MvPolynomial σ ℚ) :
    aeval (fun q => π (X q)) G = π (map (algebraMap ℚ ℂ) G) := by sorry
