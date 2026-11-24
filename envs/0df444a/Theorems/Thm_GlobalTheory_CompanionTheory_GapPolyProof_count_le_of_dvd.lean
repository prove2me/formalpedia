-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_count_le_of_dvd
-- name    : GlobalTheory.CompanionTheory.GapPolyProof.count_le_of_dvd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:46.270807+00:00
-- url     : https://prove2.me/theorems/eaf4e561-5561-4f0e-a783-9745485bcb3e
-- title:
--   Gap Poly Proof: count le of dvd
-- statement:
--   The Gap Poly Proof construction uses the count le of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean#L121-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean#L121-L154

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem GlobalTheory.CompanionTheory.GapPolyProof.count_le_of_dvd (S : Multiset ℂ) (q c d z : ℂ) (hq : q ≠ 0) (hc : c ≠ 0) (f : ℂ[X])
    (hf : (X - C z) ^ (S.count z) ∣ f)
    (hrel : C d * (X * f) = C c * (((S.map (fun t => X - C t)).prod).comp (C q * X) - (S.map (fun t => X - C t)).prod)) :
    S.count z ≤ S.count (q * z) := by sorry
