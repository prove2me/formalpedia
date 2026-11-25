-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Top_affCoord_rep
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.affCoord_rep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:13:39.065885+00:00
-- url     : https://prove2.me/theorems/3c62a3cd-0278-5c5e-91c8-8ec313b51e69
-- title:
--   Top: aff Coord rep
-- statement:
--   The Top construction uses the aff Coord rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCompactEmbedded.lean#L90-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCompactEmbedded.lean#L90-L99

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.affCoord_rep (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    affCoord p (rep x) q = x.1 ⟨q.1, (q.2, p q.1)⟩ / x.1 ⟨q.1, (p q.1, p q.1)⟩ := by sorry
