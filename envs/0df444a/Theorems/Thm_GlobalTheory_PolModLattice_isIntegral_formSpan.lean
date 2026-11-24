-- Prove2me | Theorems.Thm_GlobalTheory_PolModLattice_isIntegral_formSpan
-- name    : GlobalTheory.PolModLattice.isIntegral_formSpan
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:59.341809+00:00
-- url     : https://prove2.me/theorems/3652d2dc-8630-4cc2-9996-1a2feeb3f247
-- title:
--   Pol Mod Lattice: is Integral form Span
-- statement:
--   The Pol Mod Lattice construction uses the is Integral form Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean#L136-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean#L136-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.PolModLattice.isIntegral_formSpan (L : Submodule (OF E) E) (N : ℕ) (hN : ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) :
    ∀ w ∈ formSpan L, IsIntegral ℤ ((N : E) ^ 2 * w) := by sorry
