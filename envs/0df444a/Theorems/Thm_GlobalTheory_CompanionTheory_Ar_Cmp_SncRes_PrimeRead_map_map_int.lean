-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_PrimeRead_map_map_int
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.map_map_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:37:23.863694+00:00
-- url     : https://prove2.me/theorems/bde40afc-467c-45b2-87b8-54a85e7931fd
-- title:
--   Prime Read: map map int
-- statement:
--   The Prime Read construction uses the map map int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L37-L40

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.map_map_int {σ : Type} (g : MvPolynomial σ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by sorry
