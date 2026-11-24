-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dvd_minpoly_mul
-- name    : GlobalTheory.CompanionTheory.GapPolyProof.dvd_minpoly_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:27.631801+00:00
-- url     : https://prove2.me/theorems/17c9dc4a-a22b-40c3-a800-a67d5ea08f91
-- title:
--   Gap Poly Proof: dvd minpoly mul
-- statement:
--   The Gap Poly Proof construction uses the dvd minpoly mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean#L95-L102

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

theorem GlobalTheory.CompanionTheory.GapPolyProof.dvd_minpoly_mul [FiniteDimensional ℂ E] (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1)
    (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x)
    (ψ : E →ₗ[ℂ] ℂ) :
    (S.map (fun t => X - C t)).prod ∣ minpoly ℂ T * dd n v ψ := by sorry
