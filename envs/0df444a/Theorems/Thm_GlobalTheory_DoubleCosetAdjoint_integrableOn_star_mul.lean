-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_integrableOn_star_mul
-- name    : GlobalTheory.DoubleCosetAdjoint.integrableOn_star_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:03.456899+00:00
-- url     : https://prove2.me/theorems/a5b92fcc-9d5d-485a-a581-9a879c4ade7f
-- title:
--   Double Coset Adjoint: integrable On star mul
-- statement:
--   The Double Coset Adjoint construction uses the integrable On star mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L47-L54

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
omit [Group H] [IsTopologicalGroup H] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

theorem GlobalTheory.DoubleCosetAdjoint.integrableOn_star_mul (F F' : H → ℂ) (hF : Continuous F) (hF' : Continuous F')
    (h1 : IntegrableOn (fun h => star (F h) * F h) 𝓕 μ)
    (h2 : IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ) :
    IntegrableOn (fun h => star (F h) * F' h) 𝓕 μ := by sorry
