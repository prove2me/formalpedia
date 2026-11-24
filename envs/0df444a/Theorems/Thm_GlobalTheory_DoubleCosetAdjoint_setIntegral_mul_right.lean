-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_setIntegral_mul_right
-- name    : GlobalTheory.DoubleCosetAdjoint.setIntegral_mul_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:16.938743+00:00
-- url     : https://prove2.me/theorems/a3286e73-2f0f-446d-9103-eefedeedb243
-- title:
--   Double Coset Adjoint: set Integral mul right
-- statement:
--   The Double Coset Adjoint construction uses the set Integral mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L25-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.DoubleCosetAdjoint
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)

theorem GlobalTheory.DoubleCosetAdjoint.setIntegral_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by sorry
