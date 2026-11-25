-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hk_mul
-- name    : GlobalTheory.CompanionTheory.HeckeMul.hk_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:22.876086+00:00
-- url     : https://prove2.me/theorems/f5e1cc3f-8c93-4d31-bd3e-36cd5ee7711a
-- title:
--   Hecke Mul: hk mul
-- statement:
--   The Hecke Mul construction uses the hk mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L163-L165

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul

theorem GlobalTheory.CompanionTheory.HeckeMul.hk_mul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ), IsHk K e₁ → IsHk K e₂ → IsHk K (hconv K e₁ e₂) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K, hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) := by sorry
