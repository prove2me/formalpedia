-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_preimage_preimage_mul
-- name    : GlobalTheory.DoubleCosetAdjoint.preimage_preimage_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:37.332568+00:00
-- url     : https://prove2.me/theorems/98fdc9af-7f0d-4f1b-a36c-4303a535f35c
-- title:
--   Double Coset Adjoint: preimage preimage mul
-- statement:
--   The Double Coset Adjoint construction uses the preimage preimage mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L21-L23

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
omit [μ.IsMulLeftInvariant] [Countable Γ] [μ.IsMulRightInvariant] [TopologicalSpace H]
  [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]

theorem GlobalTheory.DoubleCosetAdjoint.preimage_preimage_mul (y : H) :
    (fun h => h * y) ⁻¹' ((fun h => h * y⁻¹) ⁻¹' 𝓕) = 𝓕 := by sorry
