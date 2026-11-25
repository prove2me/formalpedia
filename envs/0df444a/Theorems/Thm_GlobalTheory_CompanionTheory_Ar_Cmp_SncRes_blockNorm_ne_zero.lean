-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_blockNorm_ne_zero
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.blockNorm_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:23.755943+00:00
-- url     : https://prove2.me/theorems/50d3dd9c-90e7-55c7-8016-65f6cda68c93
-- title:
--   Snc Res: block Norm ne zero
-- statement:
--   The Snc Res construction uses the block Norm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCoverAndCone.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCoverAndCone.lean#L43-L48

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.blockNorm_ne_zero {z : (Σ k, ι k) → ℂ} {k : K} {j : ι k} (hj : z ⟨k, j⟩ ≠ 0) :
    ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by sorry
