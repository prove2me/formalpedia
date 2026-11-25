-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_lift_vec
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.lift_vec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:17:36.676263+00:00
-- url     : https://prove2.me/theorems/25fa075c-fde8-44e2-a30d-37ec5ef9336f
-- title:
--   Snc Res: lift vec
-- statement:
--   The Snc Res construction uses the lift vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCoverAndCone.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCoverAndCone.lean#L80-L83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.lift_vec {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) (x : Pts P)
    (hx : x ∈ src P p) :
    (fun q => eval (coord P p x) (lift p q)) = affCoord p (rep x) := by sorry
