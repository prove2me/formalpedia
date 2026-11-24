-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_range_le_isoPart
-- name    : GlobalTheory.CompanionTheory.AdmGL.range_le_isoPart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:16:41.911824+00:00
-- url     : https://prove2.me/theorems/af870681-c398-4d42-ae34-8082fcad3bbb
-- title:
--   Adm GL: range le iso Part
-- statement:
--   The Adm GL construction uses the range le iso Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem GlobalTheory.CompanionTheory.AdmGL.range_le_isoPart (π : K →* (H →L[ℂ] H)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) {T : W →ₗ[ℂ] H} (hT : ∀ k w, T (ρ k w) = π k (T w)) :
    LinearMap.range T ≤ isoPart π ρ := by sorry
