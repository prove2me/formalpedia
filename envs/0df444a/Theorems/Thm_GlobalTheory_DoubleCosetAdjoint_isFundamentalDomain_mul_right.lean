-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_isFundamentalDomain_mul_right
-- name    : GlobalTheory.DoubleCosetAdjoint.isFundamentalDomain_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:43.401676+00:00
-- url     : https://prove2.me/theorems/7d489cbc-fdb4-44ab-837c-d2814e53d612
-- title:
--   Double Coset Adjoint: is Fundamental Domain mul right
-- statement:
--   The Double Coset Adjoint construction uses the is Fundamental Domain mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean#L13-L17

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
omit [μ.IsMulLeftInvariant] [Countable Γ]

theorem GlobalTheory.DoubleCosetAdjoint.isFundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) ⁻¹' 𝓕) μ := by sorry
