-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Top_isOpen_alt_bis
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.isOpen_alt_bis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:52.943653+00:00
-- url     : https://prove2.me/theorems/7fdddfb9-15db-5019-b29b-2ec0157b2591
-- title:
--   Top: is Open alt bis
-- statement:
--   The Top construction uses the is Open alt bis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCompactEmbedded.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCompactEmbedded.lean#L84-L88

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.isOpen_alt_bis (p : (k : K) → ι k) : IsOpen (src P p) := by sorry
