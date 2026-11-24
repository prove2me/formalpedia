-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_integrableOn_mul_right
-- name    : GlobalTheory.DoubleCosetAdjoint.integrableOn_mul_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:15.206276+00:00
-- url     : https://prove2.me/theorems/0db28629-f96e-4445-ba73-9cb86e7fe31a
-- title:
--   Double Coset Adjoint: integrable On mul right
-- statement:
--   The Double Coset Adjoint construction uses the integrable On mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L35-L43

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

theorem GlobalTheory.DoubleCosetAdjoint.integrableOn_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by sorry
