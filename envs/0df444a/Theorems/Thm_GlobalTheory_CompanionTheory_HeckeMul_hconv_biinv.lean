-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hconv_biinv
-- name    : GlobalTheory.CompanionTheory.HeckeMul.hconv_biinv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:25.514802+00:00
-- url     : https://prove2.me/theorems/c8a18486-1853-4ae7-aa65-60fe63e6f8cd
-- title:
--   Hecke Mul: hconv biinv
-- statement:
--   The Hecke Mul construction uses the hconv biinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L70-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L70-L83

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.HeckeMul.hconv_biinv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {k₁ k₂ : GL ι F} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (g : GL ι F) :
    hconv K e₁ e₂ (k₁ * g * k₂) = hconv K e₁ e₂ g := by sorry
