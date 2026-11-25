-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Top_mem_src_iff
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.mem_src_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:03:01.814084+00:00
-- url     : https://prove2.me/theorems/80603910-5061-5378-bc86-5a490ad8bda4
-- title:
--   Top: mem src iff
-- statement:
--   The Top construction uses the mem src iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCompactEmbedded.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCompactEmbedded.lean#L76-L82

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.mem_src_iff (p : (k : K) → ι k) (x : Pts P) :
    x ∈ src P p ↔ ∀ k, x.1 ⟨k, (p k, p k)⟩ ≠ 0 := by sorry
