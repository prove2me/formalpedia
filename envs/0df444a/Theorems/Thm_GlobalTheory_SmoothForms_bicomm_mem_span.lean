-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_bicomm_mem_span
-- name    : GlobalTheory.SmoothForms.bicomm_mem_span
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:00.107223+00:00
-- url     : https://prove2.me/theorems/6182928d-4d25-457b-8285-7d661345b44c
-- title:
--   Smooth Forms: bicomm mem span
-- statement:
--   The Smooth Forms construction uses the bicomm mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BicommutantTensorFactorPermMemSpan.lean#L39-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BicommutantTensorFactorPermMemSpan.lean#L39-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms

theorem GlobalTheory.SmoothForms.bicomm_mem_span {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] [Fintype G] (ρ : G → Matrix ι ι ℂ)
    (h1 : ρ 1 = 1) (hmul : ∀ g h, ρ g * ρ h = ρ (h * g)) (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ g, T * ρ g = ρ g * T) → M * T = T * M) :
    M ∈ Submodule.span ℂ (Set.range ρ) := by sorry
