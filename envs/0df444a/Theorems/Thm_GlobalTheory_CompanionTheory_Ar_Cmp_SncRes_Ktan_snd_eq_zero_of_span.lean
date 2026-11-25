-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Ktan_snd_eq_zero_of_span
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.snd_eq_zero_of_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:34:15.465831+00:00
-- url     : https://prove2.me/theorems/50530441-dcfe-53d2-8a49-2f52c75beaa0
-- title:
--   Ktan: snd eq zero of span
-- statement:
--   The Ktan construction uses the snd eq zero of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SndEqZeroOfSpan.lean#L30-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SndEqZeroOfSpan.lean#L30-L55

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
open TrivSqZeroExt

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.snd_eq_zero_of_span {S : Type} [CommRing S] [Algebra ℚ S]
    (φ : S →ₐ[ℚ] TrivSqZeroExt ℂ ℂ) {e : ℕ} (z : Fin e → S)
    (hspan : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤)
    (h : ∀ i, snd (φ (z i)) = 0) (s : S) : snd (φ s) = 0 := by sorry
