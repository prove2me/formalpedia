-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Ktan_aeval_dualPt
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.aeval_dualPt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:50.196799+00:00
-- url     : https://prove2.me/theorems/187875dc-06ac-4837-927e-e099183f13b4
-- title:
--   Ktan: aeval dual Pt
-- statement:
--   The Ktan construction uses the aeval dual Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SndEqZeroOfSpan.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SndEqZeroOfSpan.lean#L15-L28

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.aeval_dualPt {σ : Type} [Fintype σ] (t v : σ → ℂ) (G : MvPolynomial σ ℂ) :
    fst (aeval (dualPt t v) G) = eval t G ∧
      snd (aeval (dualPt t v) G) = ∑ q, v q * eval t (pderiv q G) := by sorry
